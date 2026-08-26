#!/usr/bin/env python3
"""Automatically choose and rigorously certify a finite parity threshold.

The midpoint eigensolve in this script is heuristic only: it proposes a
threshold between the approximate even ground eigenvalue and the smaller of
(the next even eigenvalue, the odd ground eigenvalue).  The final result is
accepted only after four independent Arb interval LDL^T inertia checks, using
the cutoff-free matrix assembly in ``certify_parity_gap.py``.

The certified conclusion for one finite Galerkin matrix is

    0 < lambda_min(even) < threshold
      < min(lambda_1(even), lambda_min(odd)).

Consequently exactly one full-matrix eigenvalue lies below the threshold, so
that finite matrix has a simple even ground state.  This is not a continuum,
asymptotic, or Riemann-hypothesis statement.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import math
import os
import platform
import sys
from pathlib import Path
from typing import Iterable

import flint
import mpmath as mp
from flint import arb, arb_mat, ctx

from certify_parity_gap import (
    build_cutoff_free_matrix,
    certified_inertia,
    parity_blocks,
    reflection_symmetric_enclosure,
    require_inertia,
    result_to_json,
    shifted,
)


def midpoint_text(x: arb, digits: int) -> str:
    """Return a decimal midpoint string; this is never used as a proof."""
    return x.mid().str(digits, radius=False)


def midpoint_matrix(A: arb_mat, dps: int) -> mp.matrix:
    mp.mp.dps = dps
    rows = A.nrows()
    cols = A.ncols()
    digits = max(50, dps + 8)
    return mp.matrix(
        rows,
        cols,
        lambda i, j: mp.mpf(midpoint_text(A[i, j], digits)),
    )


def approximate_low_spectrum(A: arb_mat, dps: int, count: int) -> list[mp.mpf]:
    """High-precision midpoint spectrum, used only to propose thresholds."""
    values, _ = mp.eigsy(midpoint_matrix(A, dps))
    return [mp.mpf(values[i]) for i in range(min(count, len(values)))]


def threshold_text(value: mp.mpf, digits: int = 60) -> str:
    if not mp.isfinite(value) or value <= 0:
        raise ValueError(f"threshold must be finite and positive, got {value}")
    return mp.nstr(value, digits, min_fixed=0, max_fixed=0)


def unique_positive(values: Iterable[mp.mpf]) -> list[mp.mpf]:
    seen: set[str] = set()
    out: list[mp.mpf] = []
    for value in values:
        if not mp.isfinite(value) or value <= 0:
            continue
        key = mp.nstr(value, 80)
        if key not in seen:
            seen.add(key)
            out.append(value)
    return out


def heuristic_candidates(
    even_values: list[mp.mpf],
    odd_values: list[mp.mpf],
    max_exp: int,
) -> list[mp.mpf]:
    """Generate candidate thresholds; none of them carries proof status."""
    candidates: list[mp.mpf] = []
    if len(even_values) >= 2 and odd_values:
        low = even_values[0]
        high = min(even_values[1], odd_values[0])
        if 0 < low < high:
            log_low = mp.log10(low)
            log_high = mp.log10(high)
            for theta in (
                mp.mpf("0.25"),
                mp.mpf("0.333333333333333333333333333333333"),
                mp.mpf("0.5"),
                mp.mpf("0.666666666666666666666666666666667"),
                mp.mpf("0.75"),
            ):
                candidates.append(mp.power(10, (1 - theta) * log_low + theta * log_high))

            # Integer powers throughout the apparent gap are especially stable
            # under decimal serialization and interval reconstruction.
            upper_exp = math.ceil(float(-log_low))
            lower_exp = math.floor(float(-log_high))
            for exponent in range(max(1, lower_exp), min(max_exp, upper_exp) + 1):
                candidates.append(mp.power(10, -exponent))

    # Fallback ladder.  It is intentionally exhaustive at one decimal order per
    # step because the parity window is expected to be many orders wide.
    candidates.extend(mp.power(10, -exponent) for exponent in range(1, max_exp + 1))
    return unique_positive(candidates)


def certify_threshold(even: arb_mat, odd: arb_mat, text: str):
    t = arb(text)
    if not t > 0:
        return None
    even_shift = certified_inertia(shifted(even, t))
    odd_shift = certified_inertia(shifted(odd, t))
    if not even_shift.certified or not odd_shift.certified:
        return None
    expected_even = (even.nrows() - 1, 1)
    expected_odd = (odd.nrows(), 0)
    if (even_shift.n_pos, even_shift.n_neg) != expected_even:
        return None
    if (odd_shift.n_pos, odd_shift.n_neg) != expected_odd:
        return None
    return t, even_shift, odd_shift


def certify_auto(c: int, N: int, prec: int, max_exp: int) -> dict[str, object]:
    ctx.prec = prec
    raw = build_cutoff_free_matrix(c, N, prec)
    sym = reflection_symmetric_enclosure(raw, N)
    even, odd = parity_blocks(sym, N)

    even_zero = certified_inertia(even)
    odd_zero = certified_inertia(odd)
    require_inertia("even at zero", even_zero, (N + 1, 0))
    require_inertia("odd at zero", odd_zero, (N, 0))

    # Roughly one decimal digit per 3.322 bits, plus a guard margin.
    dps = max(80, int(prec / 3.3219280948873626) + 30)
    even_approx = approximate_low_spectrum(even, dps, 2)
    odd_approx = approximate_low_spectrum(odd, dps, 1)

    attempted: list[str] = []
    certified = None
    for candidate in heuristic_candidates(even_approx, odd_approx, max_exp):
        text = threshold_text(candidate)
        attempted.append(text)
        certified = certify_threshold(even, odd, text)
        if certified is not None:
            break

    if certified is None:
        raise RuntimeError(
            f"no certified parity threshold found after {len(attempted)} attempts; "
            f"searched through exponent {max_exp}"
        )

    threshold, even_shift, odd_shift = certified
    return {
        "status": "PASS",
        "statement": (
            "0 < lambda_min(even) < threshold < min(lambda_1(even), "
            "lambda_min(odd)); exactly one full-matrix eigenvalue lies below "
            "threshold, hence the finite ground state is simple and even"
        ),
        "scope": (
            "finite cutoff-free Galerkin matrix only; no continuum, asymptotic, "
            "operator-convergence, or Riemann-hypothesis conclusion"
        ),
        "c": c,
        "N": N,
        "full_dimension": 2 * N + 1,
        "even_dimension": N + 1,
        "odd_dimension": N,
        "prec_bits": prec,
        "midpoint_dps": dps,
        "threshold": threshold_text(mp.mpf(midpoint_text(threshold, 80)), 70),
        "heuristic_midpoint_spectrum": {
            "proof_status": "none; proposal mechanism only",
            "even_lowest_two": [mp.nstr(x, 80) for x in even_approx],
            "odd_lowest": mp.nstr(odd_approx[0], 80),
        },
        "attempt_count": len(attempted),
        "attempted_thresholds": attempted,
        "even_unshifted": result_to_json(even_zero),
        "odd_unshifted": result_to_json(odd_zero),
        "even_shifted": result_to_json(even_shift),
        "odd_shifted": result_to_json(odd_shift),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--c", type=int, required=True)
    parser.add_argument("--N", type=int, required=True)
    parser.add_argument("--prec", type=int, default=900)
    parser.add_argument("--max-exp", type=int, default=240)
    parser.add_argument("--json-out", required=True)
    args = parser.parse_args()

    if args.c < 2 or args.N < 1 or args.prec < 128 or args.max_exp < 1:
        parser.error("require c >= 2, N >= 1, prec >= 128, max-exp >= 1")

    certificate = certify_auto(args.c, args.N, args.prec, args.max_exp)
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
    print(
        json.dumps(
            {
                "status": certificate["status"],
                "c": args.c,
                "N": args.N,
                "threshold": certificate["threshold"],
                "statement": certificate["statement"],
                "json_out": str(output),
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"AUTO CERTIFICATE FAILED: {exc}", file=sys.stderr)
        raise
