#!/usr/bin/env python3
"""Rigorous generalized-eigenvalue bounds between two finite CvS forms.

For one parity block, let A0 be the cutoff-free matrix at a reference cutoff and
A1 the matrix at a target cutoff.  A high-precision midpoint LDL^T factor of A0
is used only as a fixed congruence preconditioner.  All conclusions are then
certified by Arb interval inertia counts for

    R^T (A1 - t A0) R.

The script rigorously brackets the smallest and largest generalized
eigenvalues, hence proves

    gamma_min A0 <= A1 <= gamma_max A0

in Loewner order for each parity block.  This is a finite-dimensional relative
form comparison.  It does not prove a uniform-in-cutoff or continuum theorem.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import platform
import sys
from dataclasses import dataclass
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path

import flint
from flint import arb, arb_mat, ctx

from certify_parity_gap import (
    build_cutoff_free_matrix,
    certified_inertia,
    parity_blocks,
    reflection_symmetric_enclosure,
    require_inertia,
    result_to_json,
)


@dataclass(frozen=True)
class LDLFactors:
    lower: arb_mat
    diagonal: tuple[arb, ...]


def identity(n: int) -> arb_mat:
    out = arb_mat(n, n)
    for i in range(n):
        out[i, i] = 1
    return out


def transpose(A: arb_mat) -> arb_mat:
    out = arb_mat(A.ncols(), A.nrows())
    for i in range(A.nrows()):
        for j in range(A.ncols()):
            out[j, i] = A[i, j]
    return out


def matmul(A: arb_mat, B: arb_mat) -> arb_mat:
    if A.ncols() != B.nrows():
        raise ValueError("matrix shape mismatch")
    out = arb_mat(A.nrows(), B.ncols())
    for i in range(A.nrows()):
        for j in range(B.ncols()):
            value = arb(0)
            for k in range(A.ncols()):
                value += A[i, k] * B[k, j]
            out[i, j] = value
    return out


def symmetrize(A: arb_mat) -> arb_mat:
    if A.nrows() != A.ncols():
        raise ValueError("square matrix required")
    out = arb_mat(A.nrows(), A.ncols())
    for i in range(A.nrows()):
        for j in range(i, A.ncols()):
            value = (A[i, j] + A[j, i]) / 2
            out[i, j] = value
            out[j, i] = value
    return out


def linear_combination(A: arb_mat, alpha: arb, B: arb_mat, beta: arb) -> arb_mat:
    if A.nrows() != B.nrows() or A.ncols() != B.ncols():
        raise ValueError("matrix shape mismatch")
    out = arb_mat(A.nrows(), A.ncols())
    for i in range(A.nrows()):
        for j in range(A.ncols()):
            out[i, j] = alpha * A[i, j] + beta * B[i, j]
    return out


def positive_ldlt(A: arb_mat) -> LDLFactors:
    """Interval LDL^T factors of a matrix already certified positive definite."""
    n = A.nrows()
    L = identity(n)
    D: list[arb] = [arb(0) for _ in range(n)]
    for i in range(n):
        pivot = A[i, i]
        for k in range(i):
            pivot -= L[i, k] * L[i, k] * D[k]
        if not pivot > 0:
            raise RuntimeError(f"reference LDLT pivot {i} is not strictly positive")
        D[i] = pivot
        for j in range(i + 1, n):
            value = A[j, i]
            for k in range(i):
                value -= L[j, k] * L[i, k] * D[k]
            L[j, i] = value / pivot
    return LDLFactors(L, tuple(D))


def inverse_upper(U: arb_mat) -> arb_mat:
    """Inverse of an upper triangular Arb matrix with nonzero diagonal."""
    n = U.nrows()
    if n != U.ncols():
        raise ValueError("square matrix required")
    out = arb_mat(n, n)
    for column in range(n):
        x = [arb(0) for _ in range(n)]
        for i in range(n - 1, -1, -1):
            rhs = arb(1) if i == column else arb(0)
            for k in range(i + 1, n):
                rhs -= U[i, k] * x[k]
            if U[i, i].contains_zero():
                raise RuntimeError(f"upper-triangular diagonal {i} contains zero")
            x[i] = rhs / U[i, i]
        for i in range(n):
            out[i, column] = x[i]
    return out


def midpoint_preconditioner(A: arb_mat) -> arb_mat:
    """Fixed point preconditioner R approximately satisfying R^T A R = I."""
    factors = positive_ldlt(A)
    n = A.nrows()
    Lmid = arb_mat(n, n)
    for i in range(n):
        for j in range(n):
            Lmid[i, j] = factors.lower[i, j].mid()
    Uinv = inverse_upper(transpose(Lmid))
    R = arb_mat(n, n)
    for i in range(n):
        for j in range(n):
            dmid = factors.diagonal[j].mid()
            if not dmid > 0:
                raise RuntimeError(f"midpoint diagonal {j} is not positive")
            R[i, j] = Uinv[i, j] / dmid.sqrt()
    return R


def congruence(A: arb_mat, R: arb_mat) -> arb_mat:
    return symmetrize(matmul(transpose(R), matmul(A, R)))


def fraction_decimal(value: Fraction, digits: int = 80) -> str:
    with localcontext() as context:
        context.prec = digits
        decimal = Decimal(value.numerator) / Decimal(value.denominator)
        return f"{decimal:.{digits - 1}E}"


def fraction_json(value: Fraction) -> dict[str, object]:
    return {
        "numerator": str(value.numerator),
        "denominator": str(value.denominator),
        "decimal": fraction_decimal(value),
    }


def power_fraction(exponent: int) -> Fraction:
    return Fraction(10**exponent, 1) if exponent >= 0 else Fraction(1, 10 ** (-exponent))


@dataclass(frozen=True)
class GeneralizedCount:
    threshold: Fraction
    negative_count: int
    inertia: dict[str, object]


def generalized_count(B1: arb_mat, B0: arb_mat, threshold: Fraction) -> GeneralizedCount | None:
    matrix = linear_combination(B1, arb(1), B0, -arb(threshold.numerator) / arb(threshold.denominator))
    result = certified_inertia(matrix)
    if not result.certified:
        return None
    return GeneralizedCount(threshold, result.n_neg, result_to_json(result))


def find_power_bracket(B1: arb_mat, B0: arb_mat, target: int, min_exp: int, max_exp: int):
    cache: dict[int, GeneralizedCount] = {}

    def evaluate(exponent: int) -> GeneralizedCount:
        if exponent not in cache:
            result = generalized_count(B1, B0, power_fraction(exponent))
            if result is None:
                raise RuntimeError(f"indeterminate generalized LDLT at 10^{exponent}")
            cache[exponent] = result
        return cache[exponent]

    low_exp = min_exp
    low = evaluate(low_exp)
    if low.negative_count >= target:
        raise RuntimeError(f"min-exp {min_exp} is not below generalized target {target}")

    high_exp = low_exp
    high = low
    while high_exp < max_exp and high.negative_count < target:
        low_exp, low = high_exp, high
        high_exp += 1
        high = evaluate(high_exp)
    if high.negative_count < target:
        raise RuntimeError(f"max-exp {max_exp} does not reach generalized target {target}")
    return low, high, sorted(cache)


def refine_generalized(B1: arb_mat, B0: arb_mat, target: int, low: GeneralizedCount, high: GeneralizedCount, iterations: int):
    if low.negative_count >= target or high.negative_count < target:
        raise RuntimeError("invalid generalized bracket")
    completed = 0
    termination = "iteration_limit"
    for _ in range(iterations):
        mid_value = (low.threshold + high.threshold) / 2
        mid = generalized_count(B1, B0, mid_value)
        if mid is None:
            termination = "interval_ldlt_indeterminate_at_midpoint"
            break
        if mid.negative_count >= target:
            high = mid
        else:
            low = mid
        completed += 1
    return low, high, termination, completed


def bracket_json(name: str, low: GeneralizedCount, high: GeneralizedCount, termination: str, completed: int):
    return {
        "name": name,
        "proved_interval": {
            "lower_inclusive": fraction_json(low.threshold),
            "upper_exclusive": fraction_json(high.threshold),
        },
        "relative_width_upper_bound": fraction_decimal((high.threshold - low.threshold) / low.threshold),
        "bisection_iterations_completed": completed,
        "termination": termination,
        "lower_endpoint": {
            "negative_count": low.negative_count,
            "inertia": low.inertia,
        },
        "upper_endpoint": {
            "negative_count": high.negative_count,
            "inertia": high.inertia,
        },
    }


def certify_block(A0: arb_mat, A1: arb_mat, min_exp: int, max_exp: int, iterations: int):
    reference_inertia = certified_inertia(A0)
    target_inertia = certified_inertia(A1)
    require_inertia("reference block", reference_inertia, (A0.nrows(), 0))
    require_inertia("target block", target_inertia, (A1.nrows(), 0))

    R = midpoint_preconditioner(A0)
    B0 = congruence(A0, R)
    B1 = congruence(A1, R)
    n = A0.nrows()

    min_low, min_high, min_powers = find_power_bracket(B1, B0, 1, min_exp, max_exp)
    max_low, max_high, max_powers = find_power_bracket(B1, B0, n, min_exp, max_exp)
    minimum = refine_generalized(B1, B0, 1, min_low, min_high, iterations)
    maximum = refine_generalized(B1, B0, n, max_low, max_high, iterations)

    gamma_min_lower = minimum[0].threshold
    gamma_max_upper = maximum[1].threshold
    condition_upper = gamma_max_upper / gamma_min_lower
    return {
        "dimension": n,
        "reference_unshifted": result_to_json(reference_inertia),
        "target_unshifted": result_to_json(target_inertia),
        "generalized_minimum": bracket_json(
            "gamma_min", minimum[0], minimum[1], minimum[2], minimum[3]
        ),
        "generalized_maximum": bracket_json(
            "gamma_max", maximum[0], maximum[1], maximum[2], maximum[3]
        ),
        "proved_loewner_comparison": {
            "statement": "gamma_min_lower * A0 <= A1 <= gamma_max_upper * A0",
            "gamma_min_lower": fraction_json(gamma_min_lower),
            "gamma_max_upper": fraction_json(gamma_max_upper),
            "relative_condition_number_upper_bound": fraction_json(condition_upper),
        },
        "power_exponents_evaluated": sorted(set(min_powers + max_powers)),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--c0", type=int, required=True)
    parser.add_argument("--c1", type=int, required=True)
    parser.add_argument("--N", type=int, required=True)
    parser.add_argument("--prec", type=int, default=1200)
    parser.add_argument("--min-exp", type=int, default=-8)
    parser.add_argument("--max-exp", type=int, default=8)
    parser.add_argument("--iterations", type=int, default=70)
    parser.add_argument("--json-out", required=True)
    args = parser.parse_args()

    if args.c0 < 2 or args.c1 < 2 or args.N < 1 or args.prec < 128:
        parser.error("invalid matrix parameters")
    if args.min_exp >= args.max_exp or args.iterations < 1:
        parser.error("invalid generalized-eigenvalue search parameters")

    ctx.prec = args.prec
    raw0 = build_cutoff_free_matrix(args.c0, args.N, args.prec)
    raw1 = build_cutoff_free_matrix(args.c1, args.N, args.prec)
    sym0 = reflection_symmetric_enclosure(raw0, args.N)
    sym1 = reflection_symmetric_enclosure(raw1, args.N)
    even0, odd0 = parity_blocks(sym0, args.N)
    even1, odd1 = parity_blocks(sym1, args.N)

    even_result = certify_block(
        even0, even1, args.min_exp, args.max_exp, args.iterations
    )
    odd_result = certify_block(
        odd0, odd1, args.min_exp, args.max_exp, args.iterations
    )

    certificate = {
        "status": "PASS",
        "statement": (
            "rigorous generalized-eigenvalue and Loewner-form comparison "
            "between two finite cutoff-free CvS parity blocks"
        ),
        "scope": (
            "two finite Galerkin matrices only; no continuous-cutoff, "
            "asymptotic, operator-convergence, or Riemann-hypothesis conclusion"
        ),
        "c0": args.c0,
        "c1": args.c1,
        "N": args.N,
        "prec_bits": args.prec,
        "even_block": even_result,
        "odd_block": odd_result,
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

    output = Path(args.json_out)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(certificate, indent=2) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "status": certificate["status"],
                "c0": args.c0,
                "c1": args.c1,
                "N": args.N,
                "even_condition_upper": even_result[
                    "proved_loewner_comparison"
                ]["relative_condition_number_upper_bound"]["decimal"],
                "odd_condition_upper": odd_result[
                    "proved_loewner_comparison"
                ]["relative_condition_number_upper_bound"]["decimal"],
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
        print(f"RELATIVE FORM CERTIFICATE FAILED: {exc}", file=sys.stderr)
        raise
