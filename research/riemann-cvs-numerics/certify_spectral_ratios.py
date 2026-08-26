#!/usr/bin/env python3
"""Rigorous rational brackets and parity-gap ratios for finite CvS matrices.

The script first finds power-of-ten brackets for the lowest two even and lowest
odd eigenvalues, then refines each bracket by exact rational bisection.  At every
threshold the only decision mechanism is an Arb interval LDL^T inertia count.
If a pivot becomes indeterminate, refinement stops and the last certified
bracket is retained.

The output rigorously brackets

    lambda_0(even), lambda_0(odd), lambda_1(even)

and the finite ratio

    min(lambda_0(odd), lambda_1(even)) / lambda_0(even).

All claims are finite-dimensional.  No continuum, asymptotic, convergence, or
Riemann-hypothesis conclusion is made.
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
    shifted,
)
from certify_spectral_decades import locate_transition, certify_counts


@dataclass(frozen=True)
class RationalCount:
    threshold: Fraction
    even_neg: int
    odd_neg: int
    even_json: dict[str, object]
    odd_json: dict[str, object]


def arb_fraction(value: Fraction) -> arb:
    return arb(value.numerator) / arb(value.denominator)


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


def evaluate_fraction(even: arb_mat, odd: arb_mat, value: Fraction) -> RationalCount | None:
    threshold = arb_fraction(value)
    even_result = certified_inertia(shifted(even, threshold))
    odd_result = certified_inertia(shifted(odd, threshold))
    if not even_result.certified or not odd_result.certified:
        return None
    return RationalCount(
        threshold=value,
        even_neg=even_result.n_neg,
        odd_neg=odd_result.n_neg,
        even_json=result_to_json(even_result),
        odd_json=result_to_json(odd_result),
    )


def refine_bracket(
    even: arb_mat,
    odd: arb_mat,
    parity: str,
    target: int,
    lower: Fraction,
    upper: Fraction,
    iterations: int,
) -> tuple[RationalCount, RationalCount, str, int]:
    """Refine ``lower <= eigenvalue < upper`` by certified rational bisection."""
    if not 0 < lower < upper:
        raise ValueError("invalid positive bracket")

    lower_count = evaluate_fraction(even, odd, lower)
    upper_count = evaluate_fraction(even, odd, upper)
    if lower_count is None or upper_count is None:
        raise RuntimeError("initial rational bracket is not interval-certifiable")

    def count(result: RationalCount) -> int:
        return result.even_neg if parity == "even" else result.odd_neg

    if count(lower_count) >= target or count(upper_count) < target:
        raise RuntimeError(
            f"initial {parity} bracket does not straddle target count {target}"
        )

    termination = "iteration_limit"
    completed = 0
    for _ in range(iterations):
        midpoint = (lower_count.threshold + upper_count.threshold) / 2
        midpoint_count = evaluate_fraction(even, odd, midpoint)
        if midpoint_count is None:
            termination = "interval_ldlt_indeterminate_at_midpoint"
            break
        if count(midpoint_count) >= target:
            upper_count = midpoint_count
        else:
            lower_count = midpoint_count
        completed += 1

    return lower_count, upper_count, termination, completed


def refined_json(
    name: str,
    parity: str,
    index: int,
    lower: RationalCount,
    upper: RationalCount,
    termination: str,
    completed: int,
) -> dict[str, object]:
    return {
        "name": name,
        "parity": parity,
        "zero_based_index": index,
        "proved_interval": {
            "lower_inclusive": fraction_json(lower.threshold),
            "upper_exclusive": fraction_json(upper.threshold),
        },
        "relative_width_upper_bound": fraction_decimal(
            (upper.threshold - lower.threshold) / lower.threshold
        ),
        "bisection_iterations_completed": completed,
        "termination": termination,
        "lower_endpoint_counts": {
            "even_negative_count": lower.even_neg,
            "odd_negative_count": lower.odd_neg,
            "even_inertia": lower.even_json,
            "odd_inertia": lower.odd_json,
        },
        "upper_endpoint_counts": {
            "even_negative_count": upper.even_neg,
            "odd_negative_count": upper.odd_neg,
            "even_inertia": upper.even_json,
            "odd_inertia": upper.odd_json,
        },
    }


def power_fraction(exponent: int) -> Fraction:
    return Fraction(1, 10**exponent)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--c", type=int, required=True)
    parser.add_argument("--N", type=int, required=True)
    parser.add_argument("--prec", type=int, default=1000)
    parser.add_argument("--max-exp", type=int, default=260)
    parser.add_argument("--coarse-step", type=int, default=8)
    parser.add_argument("--iterations", type=int, default=80)
    parser.add_argument("--json-out", required=True)
    args = parser.parse_args()

    if (
        args.c < 2
        or args.N < 2
        or args.prec < 128
        or args.max_exp < 1
        or args.coarse_step < 1
        or args.iterations < 1
    ):
        parser.error("invalid positive certification parameters")

    ctx.prec = args.prec
    raw = build_cutoff_free_matrix(args.c, args.N, args.prec)
    sym = reflection_symmetric_enclosure(raw, args.N)
    even, odd = parity_blocks(sym, args.N)

    even_zero = certified_inertia(even)
    odd_zero = certified_inertia(odd)
    require_inertia("even at zero", even_zero, (args.N + 1, 0))
    require_inertia("odd at zero", odd_zero, (args.N, 0))

    decade_cache = {}

    def evaluate_decade(exponent: int):
        if exponent not in decade_cache:
            decade_cache[exponent] = certify_counts(even, odd, exponent)
        return decade_cache[exponent]

    e0_no, e0_yes = locate_transition(
        1, "even", args.max_exp, args.coarse_step, evaluate_decade
    )
    e1_no, e1_yes = locate_transition(
        2, "even", args.max_exp, args.coarse_step, evaluate_decade
    )
    o0_no, o0_yes = locate_transition(
        1, "odd", args.max_exp, args.coarse_step, evaluate_decade
    )

    e0 = refine_bracket(
        even,
        odd,
        "even",
        1,
        power_fraction(e0_no.exponent),
        power_fraction(e0_yes.exponent),
        args.iterations,
    )
    e1 = refine_bracket(
        even,
        odd,
        "even",
        2,
        power_fraction(e1_no.exponent),
        power_fraction(e1_yes.exponent),
        args.iterations,
    )
    o0 = refine_bracket(
        even,
        odd,
        "odd",
        1,
        power_fraction(o0_no.exponent),
        power_fraction(o0_yes.exponent),
        args.iterations,
    )

    e0_lower, e0_upper = e0[0].threshold, e0[1].threshold
    e1_lower, e1_upper = e1[0].threshold, e1[1].threshold
    o0_lower, o0_upper = o0[0].threshold, o0[1].threshold
    barrier_lower = min(e1_lower, o0_lower)
    barrier_upper = min(e1_upper, o0_upper)
    ratio_lower = barrier_lower / e0_upper
    ratio_upper = barrier_upper / e0_lower

    certificate = {
        "status": "PASS",
        "statement": (
            "rigorous rational brackets for lambda_0(even), lambda_1(even), "
            "lambda_0(odd), and their finite barrier-to-ground ratio"
        ),
        "scope": (
            "finite cutoff-free Galerkin matrix only; no continuum, asymptotic, "
            "operator-convergence, or Riemann-hypothesis conclusion"
        ),
        "c": args.c,
        "N": args.N,
        "full_dimension": 2 * args.N + 1,
        "even_dimension": args.N + 1,
        "odd_dimension": args.N,
        "prec_bits": args.prec,
        "requested_bisection_iterations": args.iterations,
        "even_unshifted": result_to_json(even_zero),
        "odd_unshifted": result_to_json(odd_zero),
        "even_ground": refined_json(
            "lambda_0(even)", "even", 0, e0[0], e0[1], e0[2], e0[3]
        ),
        "even_first_excited": refined_json(
            "lambda_1(even)", "even", 1, e1[0], e1[1], e1[2], e1[3]
        ),
        "odd_ground": refined_json(
            "lambda_0(odd)", "odd", 0, o0[0], o0[1], o0[2], o0[3]
        ),
        "barrier_to_ground_ratio": {
            "barrier": "min(lambda_1(even), lambda_0(odd))",
            "proved_lower_bound": fraction_json(ratio_lower),
            "proved_upper_bound": fraction_json(ratio_upper),
        },
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
                "c": args.c,
                "N": args.N,
                "even_ground": certificate["even_ground"]["proved_interval"],
                "odd_ground": certificate["odd_ground"]["proved_interval"],
                "even_first_excited": certificate["even_first_excited"][
                    "proved_interval"
                ],
                "barrier_to_ground_ratio": certificate[
                    "barrier_to_ground_ratio"
                ],
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
        print(f"RATIO CERTIFICATE FAILED: {exc}", file=sys.stderr)
        raise
