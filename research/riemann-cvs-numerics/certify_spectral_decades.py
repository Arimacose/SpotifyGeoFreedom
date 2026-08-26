#!/usr/bin/env python3
"""Rigorous power-of-ten brackets for the first parity eigenvalues.

For one cutoff-free finite CvS/CCM Galerkin matrix, this script uses Arb
interval LDL^T inertia counts at thresholds 10^{-k} to bracket

* the lowest even eigenvalue;
* the second even eigenvalue;
* the lowest odd eigenvalue.

No midpoint eigensolver is used.  Every endpoint is certified by a strictly
signed interval factorization.  The output also gives a rigorous lower bound on

    min(lambda_1(even), lambda_0(odd)) / lambda_0(even),

which is the finite spectral separation relevant to Temple-type estimates.
The result is finite-dimensional only and has no continuum or RH implication.
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


@dataclass(frozen=True)
class CountPair:
    exponent: int
    even_neg: int
    odd_neg: int
    even_json: dict[str, object]
    odd_json: dict[str, object]


def power_text(exponent: int) -> str:
    return f"1e-{exponent}"


def certify_counts(even: arb_mat, odd: arb_mat, exponent: int) -> CountPair:
    threshold = arb(power_text(exponent))
    even_result = certified_inertia(shifted(even, threshold))
    odd_result = certified_inertia(shifted(odd, threshold))
    if not even_result.certified:
        raise RuntimeError(
            f"even LDLT indeterminate at 10^-{exponent}, "
            f"pivot {even_result.undetermined_pivot}"
        )
    if not odd_result.certified:
        raise RuntimeError(
            f"odd LDLT indeterminate at 10^-{exponent}, "
            f"pivot {odd_result.undetermined_pivot}"
        )
    return CountPair(
        exponent=exponent,
        even_neg=even_result.n_neg,
        odd_neg=odd_result.n_neg,
        even_json=result_to_json(even_result),
        odd_json=result_to_json(odd_result),
    )


def locate_transition(
    target: int,
    parity: str,
    max_exp: int,
    coarse_step: int,
    evaluate,
) -> tuple[CountPair, CountPair]:
    """Return adjacent certified endpoints bracketing the target eigenvalue.

    The first result has fewer than ``target`` negative eigenvalues and is the
    lower threshold endpoint.  The second has at least ``target`` negative
    eigenvalues and is the upper threshold endpoint.
    """
    if parity not in {"even", "odd"}:
        raise ValueError(parity)

    def count(pair: CountPair) -> int:
        return pair.even_neg if parity == "even" else pair.odd_neg

    upper_exp = max_exp
    upper_pair = evaluate(upper_exp)
    if count(upper_pair) >= target:
        raise RuntimeError(
            f"max-exp {max_exp} is insufficient: {parity} already has "
            f"{count(upper_pair)} negative eigenvalues at 10^-{max_exp}"
        )

    lower_exp = upper_exp
    lower_pair = upper_pair
    while lower_exp > 0 and count(lower_pair) < target:
        upper_exp = lower_exp
        upper_pair = lower_pair
        lower_exp = max(0, lower_exp - coarse_step)
        lower_pair = evaluate(lower_exp)

    if count(lower_pair) < target:
        raise RuntimeError(
            f"failed to reach the {target}-th {parity} eigenvalue by threshold 1"
        )

    # We now have count(upper_pair) < target <= count(lower_pair), with
    # lower_exp < upper_exp.  Binary search until the exponents are adjacent.
    yes_exp = lower_exp
    yes_pair = lower_pair
    no_exp = upper_exp
    no_pair = upper_pair
    while no_exp - yes_exp > 1:
        mid = (yes_exp + no_exp) // 2
        pair = evaluate(mid)
        if count(pair) >= target:
            yes_exp = mid
            yes_pair = pair
        else:
            no_exp = mid
            no_pair = pair

    # 10^{-no_exp} is the smaller threshold with too few negatives;
    # 10^{-yes_exp} is the next larger decade with enough negatives.
    return no_pair, yes_pair


def endpoint_json(pair: CountPair) -> dict[str, object]:
    return {
        "exponent": pair.exponent,
        "threshold": power_text(pair.exponent),
        "even_negative_count": pair.even_neg,
        "odd_negative_count": pair.odd_neg,
        "even_inertia": pair.even_json,
        "odd_inertia": pair.odd_json,
    }


def bracket_json(
    name: str,
    target_index: int,
    parity: str,
    lower_pair: CountPair,
    upper_pair: CountPair,
) -> dict[str, object]:
    return {
        "name": name,
        "parity": parity,
        "zero_based_index": target_index,
        "proved_interval": (
            f"[{power_text(lower_pair.exponent)}, "
            f"{power_text(upper_pair.exponent)})"
        ),
        "lower_endpoint": endpoint_json(lower_pair),
        "upper_endpoint": endpoint_json(upper_pair),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--c", type=int, required=True)
    parser.add_argument("--N", type=int, required=True)
    parser.add_argument("--prec", type=int, default=900)
    parser.add_argument("--max-exp", type=int, default=240)
    parser.add_argument("--coarse-step", type=int, default=8)
    parser.add_argument("--json-out", required=True)
    args = parser.parse_args()

    if (
        args.c < 2
        or args.N < 2
        or args.prec < 128
        or args.max_exp < 1
        or args.coarse_step < 1
    ):
        parser.error(
            "require c >= 2, N >= 2, prec >= 128, max-exp >= 1, "
            "coarse-step >= 1"
        )

    ctx.prec = args.prec
    raw = build_cutoff_free_matrix(args.c, args.N, args.prec)
    sym = reflection_symmetric_enclosure(raw, args.N)
    even, odd = parity_blocks(sym, args.N)

    even_zero = certified_inertia(even)
    odd_zero = certified_inertia(odd)
    require_inertia("even at zero", even_zero, (args.N + 1, 0))
    require_inertia("odd at zero", odd_zero, (args.N, 0))

    cache: dict[int, CountPair] = {}

    def evaluate(exponent: int) -> CountPair:
        if exponent not in cache:
            cache[exponent] = certify_counts(even, odd, exponent)
        return cache[exponent]

    e0_low, e0_high = locate_transition(
        1, "even", args.max_exp, args.coarse_step, evaluate
    )
    e1_low, e1_high = locate_transition(
        2, "even", args.max_exp, args.coarse_step, evaluate
    )
    o0_low, o0_high = locate_transition(
        1, "odd", args.max_exp, args.coarse_step, evaluate
    )

    # Rigorous lower bound for barrier / ground:
    # barrier >= min(10^-e1_low.exp, 10^-o0_low.exp)
    # ground < 10^-e0_high.exp.
    barrier_lower_exp = max(e1_low.exponent, o0_low.exponent)
    ground_upper_exp = e0_high.exponent
    separation_power = ground_upper_exp - barrier_lower_exp
    if separation_power < 0:
        raise RuntimeError(
            "certified decade brackets do not establish barrier above ground"
        )

    certificate = {
        "status": "PASS",
        "statement": (
            "rigorous power-of-ten brackets for the first two even and first "
            "odd eigenvalues of one finite cutoff-free Galerkin matrix"
        ),
        "scope": (
            "finite matrix only; no continuum, asymptotic, operator-convergence, "
            "or Riemann-hypothesis conclusion"
        ),
        "c": args.c,
        "N": args.N,
        "full_dimension": 2 * args.N + 1,
        "even_dimension": args.N + 1,
        "odd_dimension": args.N,
        "prec_bits": args.prec,
        "max_exp": args.max_exp,
        "coarse_step": args.coarse_step,
        "even_unshifted": result_to_json(even_zero),
        "odd_unshifted": result_to_json(odd_zero),
        "even_ground": bracket_json(
            "lambda_0(even)", 0, "even", e0_low, e0_high
        ),
        "even_first_excited": bracket_json(
            "lambda_1(even)", 1, "even", e1_low, e1_high
        ),
        "odd_ground": bracket_json(
            "lambda_0(odd)", 0, "odd", o0_low, o0_high
        ),
        "barrier_to_ground_lower_bound": {
            "barrier": "min(lambda_1(even), lambda_0(odd))",
            "proved_lower_bound": f"1e{separation_power}",
            "derivation": (
                f"barrier >= 1e-{barrier_lower_exp}, "
                f"lambda_0(even) < 1e-{ground_upper_exp}"
            ),
        },
        "evaluated_exponents": sorted(cache),
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
                "even_first_excited": certificate["even_first_excited"][
                    "proved_interval"
                ],
                "odd_ground": certificate["odd_ground"]["proved_interval"],
                "barrier_to_ground_lower_bound": certificate[
                    "barrier_to_ground_lower_bound"
                ]["proved_lower_bound"],
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
        print(f"DECADE CERTIFICATE FAILED: {exc}", file=sys.stderr)
        raise
