#!/usr/bin/env python3
"""Certify Loewner ordering between the nonconstant even block and odd block.

Let E be the orthonormal even parity block of the finite cutoff-free CvS/CCM
matrix and let C be the principal submatrix obtained by deleting the constant
mode.  The odd block O has the same dimension as C.  This script interval-
certifies the inertia of O-C and C-O.

A positive-semidefinite ordering, if present, would combine with ordinary
Cauchy interlacing to give a structural parity comparison.  Failure is also
informative: it rules out this simplest block-order mechanism.  Every result is
finite-dimensional only.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import platform
import sys
from pathlib import Path

import flint
from flint import arb_mat, ctx

from certify_parity_gap import (
    build_cutoff_free_matrix,
    certified_inertia,
    parity_blocks,
    reflection_symmetric_enclosure,
    result_to_json,
)


def principal_nonconstant_even(even: arb_mat) -> arb_mat:
    n = even.nrows() - 1
    out = arb_mat(n, n)
    for i in range(n):
        for j in range(n):
            out[i, j] = even[i + 1, j + 1]
    return out


def difference(A: arb_mat, B: arb_mat) -> arb_mat:
    if A.nrows() != B.nrows() or A.ncols() != B.ncols():
        raise ValueError("matrix shape mismatch")
    out = arb_mat(A.nrows(), A.ncols())
    for i in range(A.nrows()):
        for j in range(A.ncols()):
            out[i, j] = A[i, j] - B[i, j]
    return out


def classification(result, dimension: int) -> str:
    if not result.certified:
        return "INDETERMINATE"
    if (result.n_pos, result.n_neg) == (dimension, 0):
        return "POSITIVE_DEFINITE"
    if (result.n_pos, result.n_neg) == (0, dimension):
        return "NEGATIVE_DEFINITE"
    return "INDEFINITE"


def certify(c: int, N: int, prec: int) -> dict[str, object]:
    ctx.prec = prec
    raw = build_cutoff_free_matrix(c, N, prec)
    sym = reflection_symmetric_enclosure(raw, N)
    even, odd = parity_blocks(sym, N)
    nonconstant_even = principal_nonconstant_even(even)

    odd_minus_even = certified_inertia(difference(odd, nonconstant_even))
    even_minus_odd = certified_inertia(difference(nonconstant_even, odd))

    return {
        "status": "PASS",
        "statement": (
            "certified inertia test for O-C and C-O, where C is the "
            "nonconstant even principal block and O is the odd block"
        ),
        "scope": "one finite cutoff-free Galerkin matrix only",
        "c": c,
        "N": N,
        "dimension": N,
        "prec_bits": prec,
        "odd_minus_nonconstant_even": {
            "classification": classification(odd_minus_even, N),
            "inertia": result_to_json(odd_minus_even),
        },
        "nonconstant_even_minus_odd": {
            "classification": classification(even_minus_odd, N),
            "inertia": result_to_json(even_minus_odd),
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--c", type=int, required=True)
    parser.add_argument("--N", type=int, required=True)
    parser.add_argument("--prec", type=int, default=900)
    parser.add_argument("--json-out", required=True)
    args = parser.parse_args()
    if args.c < 2 or args.N < 1 or args.prec < 128:
        parser.error("require c >= 2, N >= 1, prec >= 128")

    certificate = certify(args.c, args.N, args.prec)
    certificate.update(
        {
            "created_at": dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds"),
            "python_version": platform.python_version(),
            "python_flint_version": flint.__version__,
            "platform": platform.platform(),
            "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "matrix_script_sha256": hashlib.sha256(
                (Path(__file__).parent / "certify_parity_gap.py").read_bytes()
            ).hexdigest(),
            "git_sha": os.environ.get("GITHUB_SHA"),
        }
    )
    output = Path(args.json_out)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(certificate, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": certificate["status"],
        "c": args.c,
        "N": args.N,
        "O_minus_C": certificate["odd_minus_nonconstant_even"]["classification"],
        "C_minus_O": certificate["nonconstant_even_minus_odd"]["classification"],
        "json_out": str(output),
    }, indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"PARITY BLOCK ORDER CERTIFICATE FAILED: {exc}", file=sys.stderr)
        raise
