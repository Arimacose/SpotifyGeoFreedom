#!/usr/bin/env python3
"""Exact/symbolic audit for the logarithmic high-mode CvS decomposition.

Checks:
1. the pole matrix is the difference of two rank-one kernels;
2. a prime-event matrix equals the self-adjoint part of a truncated translation
   in the normalized Fourier basis;
3. explicit elementary constants are emitted for selected cutoffs.

The script audits algebra and normalization.  It does not prove the standard
coth summation formula, the discrete Hilbert-transform norm, or the digamma
series lower bound; those are proved in the accompanying research note.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp
import sympy as sp


def prime_powers_up_to(c: int) -> list[tuple[int, int]]:
    primes: list[int] = []
    for n in range(2, c + 1):
        if all(n % p for p in primes if p * p <= n):
            primes.append(n)
    out: list[tuple[int, int]] = []
    for p in primes:
        q = p
        while q <= c:
            out.append((q, p))
            q *= p
    return sorted(out)


def symbolic_checks() -> dict[str, bool]:
    L, m, n, pi = sp.symbols(
        "L m n pi", nonzero=True, real=True
    )
    den_m = L**2 + 16 * pi**2 * m**2
    den_n = L**2 + 16 * pi**2 * n**2
    a_m = L / den_m
    a_n = L / den_n
    b_m = 4 * pi * m / den_m
    b_n = 4 * pi * n / den_n
    pole_entry = (
        L**2 - 16 * pi**2 * m * n
    ) / (den_m * den_n)
    assert sp.simplify(pole_entry - (a_m * a_n - b_m * b_n)) == 0

    alpha, beta, k = sp.symbols(
        "alpha beta k", real=True, nonzero=True
    )
    translation_entry = (
        sp.exp(sp.I * alpha) - sp.exp(sp.I * beta)
    ) / (2 * sp.pi * sp.I * k)
    symmetric_part = sp.simplify(
        translation_entry + sp.conjugate(translation_entry)
    )
    target = (
        sp.sin(alpha) - sp.sin(beta)
    ) / (sp.pi * k)
    assert sp.simplify(
        sp.expand_complex(symmetric_part - target)
    ) == 0

    return {
        "pole_rank_two_identity": True,
        "prime_translation_offdiagonal_identity": True,
    }


def numerical_translation_check() -> str:
    mp.mp.dps = 80
    max_error = mp.mpf("0")
    for L in [mp.log(5), mp.log(13), mp.mpf("3.7")]:
        for fraction in [
            mp.mpf("0.13"),
            mp.mpf("0.41"),
            mp.mpf("0.77"),
        ]:
            y = L * fraction
            for n in range(-4, 5):
                for m in range(-4, 5):
                    if n == m:
                        formula = 2 * (1 - y / L) * mp.cos(
                            2 * mp.pi * n * y / L
                        )
                        direct = 2 * mp.re(
                            (1 - y / L)
                            * mp.exp(2j * mp.pi * n * y / L)
                        )
                    else:
                        formula = (
                            mp.sin(2 * mp.pi * m * y / L)
                            - mp.sin(2 * mp.pi * n * y / L)
                        ) / (mp.pi * (n - m))
                        k = m - n
                        entry = (
                            mp.exp(2j * mp.pi * n * y / L)
                            - mp.exp(2j * mp.pi * m * y / L)
                        ) / (2j * mp.pi * k)
                        direct = entry + mp.conj(entry)
                    max_error = max(max_error, abs(formula - direct))
    assert max_error < mp.mpf("1e-70")
    return mp.nstr(max_error, 20)


def constants(c: int) -> dict[str, object]:
    mp.mp.dps = 100
    L = mp.log(c)
    a = mp.mpf(1) / 4
    R = mp.exp(-L / 2) / (1 - mp.exp(-2 * L))
    kappa = (
        mp.log(4 * mp.pi * (c - 1) / (c + 1)) + mp.euler
    )
    U = mp.sqrt(c)
    J = (
        -2 * mp.log(U + 1)
        + mp.log(U * U + 1)
        + 2 * mp.atan(U)
        + 2 * mp.log(2)
        - mp.pi / 2
    )
    C_psi = mp.euler + mp.mpf(4) / 5 + mp.log(mp.mpf(8) / 5)
    D_L = (
        C_psi
        + mp.digamma(a)
        + kappa
        + J
        + 8 * R
        + 8 * R / L
        + mp.polygamma(1, a) / (2 * L)
        + mp.log(L / mp.pi)
    )
    prime_weight = mp.fsum(
        mp.log(p) / mp.sqrt(q)
        for q, p in prime_powers_up_to(c)
    )
    S_bound = 1 + mp.pi / 4 + R
    arch_bound = 2 * S_bound
    pole_bound = 4 * mp.sinh(L / 2)
    prime_bound = 2 * prime_weight

    def text(x: mp.mpf) -> str:
        return mp.nstr(x, 50)

    return {
        "c": c,
        "L": text(L),
        "R_L": text(R),
        "C_psi": text(C_psi),
        "D_L": text(D_L),
        "S_sup_bound": text(S_bound),
        "arch_offdiagonal_bound": text(arch_bound),
        "pole_norm_bound": text(pole_bound),
        "prime_weight_sum": text(prime_weight),
        "prime_norm_bound": text(prime_bound),
        "bounded_perturbation_B_L": text(
            arch_bound + pole_bound + prime_bound
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json-out", type=Path, required=True)
    args = parser.parse_args()

    result = {
        "status": "PASS",
        "scope": (
            "Exact algebra and high-precision normalization audit; "
            "not an RH claim."
        ),
        "symbolic": symbolic_checks(),
        "translation_max_error": numerical_translation_check(),
        "constants": [constants(c) for c in [5, 13, 29, 100]],
    }
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(
        json.dumps(result, indent=2), encoding="utf-8"
    )
    print(
        json.dumps(
            {
                "status": result["status"],
                "translation_max_error": result[
                    "translation_max_error"
                ],
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
