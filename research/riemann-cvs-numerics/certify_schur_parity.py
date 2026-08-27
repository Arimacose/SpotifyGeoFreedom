#!/usr/bin/env python3
"""Rigorous finite Schur-parity certificate for the cutoff-free CvS matrix.

For the odd parity block, split the first ``low_dim`` modes from the remaining
high modes.  Certify:

* a lower bound ``ell`` for the odd low block by interval LDL^T;
* a lower bound ``gamma`` for the odd high block by interval LDL^T;
* a coupling bound ``epsilon^2 <= ||B||_F^2``;
* the normalized two-block lower bound

      lambda_min(Q_odd) >= ell - 2 ||B||_F^2 / gamma,

  provided this target does not exceed ``gamma / 2``;
* an interval Rayleigh upper bound for an embedded even low-block vector.

If the even upper bound is strictly smaller than the odd lower bound, the finite
cutoff-free Galerkin matrix has strict even/odd ground-state ordering.

The script certifies only the supplied finite matrix.  It does not establish an
infinite-operator limit or the Riemann hypothesis.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

import mpmath as mp
from flint import arb, arb_mat, ctx

from certify_parity_gap import build_arb_tau, certified_inertia


def _mp_mid(x: arb) -> mp.mpf:
    """Convert the midpoint of an Arb ball to an mpmath number."""
    return mp.mpf(str(x.mid()))


def _point_arb(x: mp.mpf, digits: int) -> arb:
    """Create a zero-radius Arb point from an mpmath value."""
    return arb(mp.nstr(x, n=digits, strip_zeros=False))


def _lower_point(x: arb) -> arb:
    """Return the lower endpoint as a zero-radius Arb point."""
    return arb(str(x.lower()))


def _upper_point(x: arb) -> arb:
    """Return the upper endpoint as a zero-radius Arb point."""
    return arb(str(x.upper()))


def _submatrix(A: arb_mat, rows: list[int], cols: list[int]) -> arb_mat:
    B = arb_mat(len(rows), len(cols))
    for i, r in enumerate(rows):
        for j, c in enumerate(cols):
            B[i, j] = A[r, c]
    return B


def _shifted(A: arb_mat, shift: arb) -> arb_mat:
    n = A.nrows()
    B = arb_mat(n, n)
    for i in range(n):
        for j in range(n):
            B[i, j] = A[i, j]
        B[i, i] -= shift
    return B


def _midpoint_matrix(A: arb_mat, dps: int) -> mp.matrix:
    mp.mp.dps = dps
    M = mp.matrix(A.nrows(), A.ncols())
    for i in range(A.nrows()):
        for j in range(A.ncols()):
            M[i, j] = _mp_mid(A[i, j])
    return M


def _smallest_midpoint_eigenpair(
    A: arb_mat, dps: int
) -> tuple[mp.mpf, list[mp.mpf]]:
    M = _midpoint_matrix(A, dps)
    vals, vecs = mp.eigsy(M)
    return mp.mpf(vals[0]), [mp.mpf(vecs[i, 0]) for i in range(A.nrows())]


def _rayleigh_ball(A: arb_mat, vector: list[arb]) -> arb:
    n = A.nrows()
    assert len(vector) == n
    numerator = arb(0)
    denominator = arb(0)
    for i in range(n):
        denominator += vector[i] * vector[i]
        for j in range(n):
            numerator += vector[i] * A[i, j] * vector[j]
    if not denominator > 0:
        raise RuntimeError(
            f"Rayleigh denominator is not certified positive: {denominator}"
        )
    return numerator / denominator


def _frobenius_sq(B: arb_mat) -> arb:
    total = arb(0)
    for i in range(B.nrows()):
        for j in range(B.ncols()):
            total += B[i, j] * B[i, j]
    return total


def _parity_blocks(A: arb_mat, N: int) -> tuple[arb_mat, arb_mat]:
    """Return exact even and odd blocks in the real reflection basis."""
    center = N
    sqrt2 = arb(2).sqrt()

    even = arb_mat(N + 1, N + 1)
    even[0, 0] = A[center, center]
    for j in range(1, N + 1):
        even[0, j] = (
            A[center, center + j] + A[center, center - j]
        ) / sqrt2
        even[j, 0] = even[0, j]
    for i in range(1, N + 1):
        for j in range(1, N + 1):
            even[i, j] = (
                A[center + i, center + j]
                + A[center + i, center - j]
                + A[center - i, center + j]
                + A[center - i, center - j]
            ) / 2

    odd = arb_mat(N, N)
    for i in range(1, N + 1):
        for j in range(1, N + 1):
            odd[i - 1, j - 1] = (
                A[center + i, center + j]
                - A[center + i, center - j]
                - A[center - i, center + j]
                + A[center - i, center - j]
            ) / 2
    return even, odd


def _inertia(A: arb_mat) -> dict[str, Any]:
    result = certified_inertia(A, A.nrows(), heartbeat=0)
    if len(result) != 4:
        raise RuntimeError(
            f"Unexpected certified_inertia return value: {result!r}"
        )
    n_pos, n_neg, undetermined, transcript = result
    transcript_text = "\n".join(str(x) for x in transcript)
    return {
        "n_pos": int(n_pos),
        "n_neg": int(n_neg),
        "undetermined_pivot": (
            None if undetermined is None else int(undetermined)
        ),
        "pivot_sha256": hashlib.sha256(
            transcript_text.encode("utf-8")
        ).hexdigest(),
        "pivot_count": len(transcript),
    }


def _certified_positive(A: arb_mat) -> tuple[bool, dict[str, Any]]:
    data = _inertia(A)
    ok = (
        data["n_pos"] == A.nrows()
        and data["n_neg"] == 0
        and data["undetermined_pivot"] is None
    )
    return ok, data


def _ball_record(x: arb) -> dict[str, str]:
    return {
        "ball": str(x),
        "lower": str(x.lower()),
        "upper": str(x.upper()),
    }


def certify(
    *,
    c: int,
    N: int,
    low_dim: int,
    prec: int,
    low_factor: str,
    high_factor: str,
) -> dict[str, Any]:
    if not (1 <= low_dim < N):
        raise ValueError("low_dim must satisfy 1 <= low_dim < N")

    ctx.prec = prec
    mp_dps = max(80, int(prec * 0.30103) + 30)
    digits = max(60, int(prec * 0.30103) - 10)

    tau, dim = build_arb_tau(c, N, prec)
    if dim != 2 * N + 1:
        raise RuntimeError(f"Unexpected full dimension: {dim}")
    even, odd = _parity_blocks(tau, N)

    even_low = _submatrix(
        even, list(range(low_dim)), list(range(low_dim))
    )
    odd_low = _submatrix(
        odd, list(range(low_dim)), list(range(low_dim))
    )
    odd_high = _submatrix(
        odd, list(range(low_dim, N)), list(range(low_dim, N))
    )
    odd_coupling = _submatrix(
        odd, list(range(low_dim, N)), list(range(low_dim))
    )

    even_eval_mid, even_vec_mid = _smallest_midpoint_eigenpair(
        even_low, mp_dps
    )
    even_vec = [_point_arb(x, digits) for x in even_vec_mid]
    even_rayleigh = _rayleigh_ball(even_low, even_vec)
    even_upper = _upper_point(even_rayleigh)

    odd_low_eval_mid, _ = _smallest_midpoint_eigenpair(
        odd_low, mp_dps
    )
    odd_high_eval_mid, _ = _smallest_midpoint_eigenpair(
        odd_high, mp_dps
    )
    if not (odd_low_eval_mid > 0 and odd_high_eval_mid > 0):
        raise RuntimeError(
            "Midpoint eigenvalues must be positive: "
            f"low={odd_low_eval_mid}, high={odd_high_eval_mid}"
        )

    low_threshold_mp = mp.mpf(low_factor) * odd_low_eval_mid
    high_gap_mp = mp.mpf(high_factor) * odd_high_eval_mid
    low_threshold = _point_arb(low_threshold_mp, digits)
    high_gap = _point_arb(high_gap_mp, digits)

    low_ok, low_inertia = _certified_positive(
        _shifted(odd_low, low_threshold)
    )
    high_ok, high_inertia = _certified_positive(
        _shifted(odd_high, high_gap)
    )

    frob_sq = _frobenius_sq(odd_coupling)
    frob_sq_upper = _upper_point(frob_sq)
    correction = 2 * frob_sq_upper / high_gap
    odd_after_ball = low_threshold - correction
    odd_after_lower = _lower_point(odd_after_ball)
    high_floor = high_gap / 2

    high_floor_ok = bool(odd_after_lower <= high_floor)
    parity_ok = bool(even_upper < odd_after_lower)
    status = (
        "PASS"
        if (low_ok and high_ok and high_floor_ok and parity_ok)
        else "FAIL"
    )

    return {
        "status": status,
        "statement": (
            "For the finite cutoff-free CvS Galerkin matrix, an embedded "
            "even low-block Rayleigh value is strictly below a certified "
            "normalized Schur lower bound for the full odd parity block."
        ),
        "scope": (
            "Finite matrix only; no infinite-Galerkin convergence or "
            "Riemann-hypothesis claim."
        ),
        "c": c,
        "N": N,
        "full_dimension": dim,
        "low_dim": low_dim,
        "precision_bits": prec,
        "low_factor": low_factor,
        "high_factor": high_factor,
        "midpoint_dps": mp_dps,
        "even_low_midpoint_eigenvalue": mp.nstr(
            even_eval_mid, 40
        ),
        "odd_low_midpoint_eigenvalue": mp.nstr(
            odd_low_eval_mid, 40
        ),
        "odd_high_midpoint_eigenvalue": mp.nstr(
            odd_high_eval_mid, 40
        ),
        "even_rayleigh": _ball_record(even_rayleigh),
        "even_upper": str(even_upper),
        "odd_low_threshold": str(low_threshold),
        "odd_high_gap": str(high_gap),
        "coupling_frobenius_sq": _ball_record(frob_sq),
        "coupling_frobenius_sq_upper": str(frob_sq_upper),
        "normalized_schur_correction": str(correction),
        "odd_after_schur_ball": _ball_record(odd_after_ball),
        "odd_after_schur_lower": str(odd_after_lower),
        "odd_high_floor": str(high_floor),
        "low_ldlt": low_inertia,
        "high_ldlt": high_inertia,
        "checks": {
            "odd_low_shift_positive_definite": low_ok,
            "odd_high_shift_positive_definite": high_ok,
            "normalized_high_floor": high_floor_ok,
            "strict_even_below_odd": parity_ok,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--N", type=int, default=40)
    parser.add_argument("--low-dim", type=int, default=4)
    parser.add_argument("--prec", type=int, default=500)
    parser.add_argument("--low-factor", default="0.5")
    parser.add_argument("--high-factor", default="0.25")
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()

    result = certify(
        c=args.c,
        N=args.N,
        low_dim=args.low_dim,
        prec=args.prec,
        low_factor=args.low_factor,
        high_factor=args.high_factor,
    )
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(
        json.dumps(result, indent=2), encoding="utf-8"
    )

    print(
        json.dumps(
            {
                "status": result["status"],
                "statement": result["statement"],
                "c": result["c"],
                "N": result["N"],
                "low_dim": result["low_dim"],
                "even_upper": result["even_upper"],
                "odd_after_schur_lower": result[
                    "odd_after_schur_lower"
                ],
                "odd_high_floor": result["odd_high_floor"],
                "checks": result["checks"],
            },
            indent=2,
        )
    )

    if result["status"] != "PASS":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
