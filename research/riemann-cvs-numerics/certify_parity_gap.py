#!/usr/bin/env python3
"""Rigorous finite simple-even certificate for a cutoff-free Weil matrix.

The cutoff-free Connes--van Suijlekom / Connes--Consani--Moscovici Galerkin
matrix is assembled entrywise as Arb balls, using the closed forms and interval
remainder strategy of Akiva Groskin's MIT-licensed
`arb_ldlt_certify.py`:

  https://github.com/akivag613/connes-cvs-/blob/main/
    papers/2_guinand_weil_dictionary_tail_order/scripts/arb_ldlt_certify.py

We then use the exact reflection symmetry n -> -n to form orthonormal even and
odd blocks.  For a supplied positive threshold t, four interval LDL^T
factorizations certify:

* the unshifted even block is positive definite;
* the unshifted odd block is positive definite;
* the even block minus tI has exactly one negative eigenvalue;
* the odd block minus tI remains positive definite.

Together these statements prove, for the selected finite (c,N) matrix,

  0 < lambda_min(even) < t < lambda_min(odd),

and there is exactly one eigenvalue below t.  Hence the lowest eigenvalue of the
full finite matrix is simple and belongs to the even sector.

This is a finite interval certificate only.  It does not prove an asymptotic
statement, convergence of finite matrices, Weil positivity in the continuum,
or the Riemann Hypothesis.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import platform
import sys
import time
from dataclasses import dataclass
from typing import Iterable

import flint
from flint import acb, arb, arb_mat, ctx


SOURCE_URL = (
    "https://github.com/akivag613/connes-cvs-/blob/main/"
    "papers/2_guinand_weil_dictionary_tail_order/scripts/arb_ldlt_certify.py"
)


def prime_powers_up_to(c: int) -> list[tuple[int, int]]:
    """Return (q,p) for every prime power q=p^a <= c."""
    primes: list[int] = []
    for x in range(2, c + 1):
        if all(x % p for p in primes):
            primes.append(x)
    out: list[tuple[int, int]] = []
    for p in primes:
        q = p
        while q <= c:
            out.append((q, p))
            q *= p
    return out


def trigamma_acb(z: acb) -> acb:
    return z.polygamma(acb(1))


def geom_sums(n: int, L: arb, prec: int) -> tuple[arb, arb, arb, arb]:
    """Closed-form correction sums with a rigorous geometric tail enclosure."""
    pi = arb.pi()
    w = 2 * pi * n / L
    w2 = w * w
    g_s = arb(0)
    g_cc = arb(0)
    g_x1 = arb(0)
    g_x2 = arb(0)
    threshold = arb(2) ** (-(prec + 24))
    k = 0
    while True:
        ck = arb(2 * k) + arb("0.5")
        exp_term = (-ck * L).exp()
        den = ck * ck + w2
        g_s += exp_term / den
        if n != 0:
            g_cc += exp_term * w2 / (ck * den)
        g_x1 += exp_term * ck / den
        g_x2 += exp_term * (ck * ck - w2) / (den * den)
        if exp_term < threshold and k > 2:
            break
        k += 1

    c_next = arb(2 * (k + 1)) + arb("0.5")
    geometric_denom = 1 - (-2 * L).exp()
    tail_geo = (-c_next * L).exp() / geometric_denom
    remainder = arb(4) * tail_geo

    def widen(x: arb) -> arb:
        return x + arb(0, remainder)

    return widen(g_s), widen(g_cc), widen(g_x1), widen(g_x2)


def closed_forms(N: int, c: int, prec: int) -> tuple[list[arb], list[arb], list[arb], arb]:
    ctx.prec = prec
    L = arb(c).log()
    pi = arb.pi()
    quarter = arb("0.25")
    psi_quarter = quarter.digamma()
    S = [arb(0) for _ in range(N + 1)]
    CC = [arb(0) for _ in range(N + 1)]
    XC = [arb(0) for _ in range(N + 1)]

    for n in range(N + 1):
        w = 2 * pi * n / L
        zarg = acb(quarter, pi * n / L)
        psi = zarg.digamma()
        psi1 = trigamma_acb(zarg)
        g_s, g_cc, g_x1, g_x2 = geom_sums(n, L, prec)
        if n == 0:
            S[n] = arb(0)
            CC[n] = arb(0)
        else:
            S[n] = arb("0.5") * psi.imag - w * g_s
            CC[n] = -arb("0.5") * (psi.real - psi_quarter) + g_cc
        XC[n] = arb("0.25") * psi1.real - L * g_x1 - g_x2
    return S, CC, XC, L


def pole_J(L: arb) -> arb:
    U = (L / 2).exp()
    return (
        -2 * (U + 1).log()
        + (U * U + 1).log()
        + 2 * U.atan()
        + arb(2).log()
        - arb.pi() / 2
    )


def arch_kappa(L: arb) -> arb:
    eL = L.exp()
    return (4 * arb.pi() * (eL - 1) / (eL + 1)).log() + arb.const_euler()


def build_cutoff_free_matrix(c: int, N: int, prec: int) -> arb_mat:
    """Build tau = W_02 - W_R - W_p as a rigorous Arb matrix."""
    ctx.prec = prec
    S, CC, XC, L = closed_forms(N, c, prec)
    pi = arb.pi()
    sixteen_pi_sq = 16 * pi * pi
    L_sq = L * L
    pref_02 = 32 * L * (L / 4).sinh() ** 2
    kappa = arch_kappa(L)
    J = pole_J(L)

    prime_data = prime_powers_up_to(c)
    weights = [arb(p).log() * (arb(q) ** arb("-0.5")) for q, p in prime_data]
    positions = [arb(q).log() for q, _ in prime_data]

    def S_signed(n: int) -> arb:
        return S[n] if n >= 0 else -S[-n]

    dim = 2 * N + 1
    A = arb_mat(dim, dim)
    for i in range(dim):
        n = i - N
        for j in range(i, dim):
            m = j - N
            numerator = L_sq - sixteen_pi_sq * m * n
            denominator = (
                (L_sq + sixteen_pi_sq * m * m)
                * (L_sq + sixteen_pi_sq * n * n)
            )
            W02 = pref_02 * numerator / denominator
            if n == m:
                WR = kappa + 2 * CC[abs(n)] + J - (2 / L) * XC[abs(n)]
            else:
                WR = (S_signed(m) - S_signed(n)) / (pi * (n - m))

            Wp = arb(0)
            for weight, y in zip(weights, positions):
                if n == m:
                    q_nm = 2 * (1 - y / L) * (2 * pi * n * y / L).cos()
                else:
                    q_nm = (
                        (2 * pi * m * y / L).sin()
                        - (2 * pi * n * y / L).sin()
                    ) / (pi * (n - m))
                Wp += weight * q_nm

            value = W02 - WR - Wp
            A[i, j] = value
            A[j, i] = value
    return A


def reflection_symmetric_enclosure(A: arb_mat, N: int) -> arb_mat:
    """Enforce the exact transpose/reflection symmetry without losing enclosure.

    The exact matrix satisfies A[n,m]=A[m,n]=A[-n,-m].  Each orbit is replaced
    by the average of all interval enclosures in that orbit; because every ball
    encloses the same exact real number, the average does as well.
    """
    dim = 2 * N + 1
    B = arb_mat(dim, dim)
    visited: set[tuple[int, int]] = set()

    for i in range(dim):
        for j in range(dim):
            if (i, j) in visited:
                continue
            ri = 2 * N - i
            rj = 2 * N - j
            orbit = {(i, j), (j, i), (ri, rj), (rj, ri)}
            total = arb(0)
            for a, b in orbit:
                total += A[a, b]
            average = total / len(orbit)
            for a, b in orbit:
                B[a, b] = average
                visited.add((a, b))
    return B


def parity_blocks(A: arb_mat, N: int) -> tuple[arb_mat, arb_mat]:
    """Return exact orthonormal even and odd blocks under n -> -n."""
    idx = lambda n: n + N
    sqrt_two = arb(2).sqrt()

    even = arb_mat(N + 1, N + 1)
    odd = arb_mat(N, N)
    even[0, 0] = A[idx(0), idx(0)]

    for k in range(1, N + 1):
        val = (A[idx(0), idx(k)] + A[idx(0), idx(-k)]) / sqrt_two
        even[0, k] = val
        even[k, 0] = val

    for k in range(1, N + 1):
        for ell in range(k, N + 1):
            e_val = (
                A[idx(k), idx(ell)]
                + A[idx(k), idx(-ell)]
                + A[idx(-k), idx(ell)]
                + A[idx(-k), idx(-ell)]
            ) / 2
            o_val = (
                A[idx(k), idx(ell)]
                - A[idx(k), idx(-ell)]
                - A[idx(-k), idx(ell)]
                + A[idx(-k), idx(-ell)]
            ) / 2
            even[k, ell] = e_val
            even[ell, k] = e_val
            odd[k - 1, ell - 1] = o_val
            odd[ell - 1, k - 1] = o_val
    return even, odd


def shifted(A: arb_mat, t: arb) -> arb_mat:
    rows = A.nrows()
    B = arb_mat(rows, rows)
    for i in range(rows):
        for j in range(rows):
            B[i, j] = A[i, j] - (t if i == j else 0)
    return B


@dataclass(frozen=True)
class InertiaResult:
    n_pos: int
    n_neg: int
    undetermined_pivot: int | None
    pivots: tuple[str, ...]

    @property
    def certified(self) -> bool:
        return self.undetermined_pivot is None


def certified_inertia(A: arb_mat) -> InertiaResult:
    """Unpivoted interval LDL^T; every strictly signed pivot is a proof."""
    dim = A.nrows()
    diagonal: list[arb | None] = [None] * dim
    lower = [[arb(0) for _ in range(dim)] for _ in range(dim)]
    n_pos = 0
    n_neg = 0
    transcript: list[str] = []

    for i in range(dim):
        pivot = A[i, i]
        for k in range(i):
            assert diagonal[k] is not None
            pivot -= lower[i][k] * lower[i][k] * diagonal[k]
        diagonal[i] = pivot

        if pivot > 0:
            n_pos += 1
            sign = "+"
        elif pivot < 0:
            n_neg += 1
            sign = "-"
        else:
            return InertiaResult(n_pos, n_neg, i, tuple(transcript))

        transcript.append(
            f"{i} {sign} {pivot.mid().str(50, radius=False)} "
            f"{pivot.rad().str(12, radius=False)}"
        )
        for j in range(i + 1, dim):
            value = A[j, i]
            for k in range(i):
                assert diagonal[k] is not None
                value -= lower[j][k] * lower[i][k] * diagonal[k]
            lower[j][i] = value / pivot

    return InertiaResult(n_pos, n_neg, None, tuple(transcript))


def result_to_json(result: InertiaResult) -> dict[str, object]:
    digest = hashlib.sha256("\n".join(result.pivots).encode()).hexdigest()
    return {
        "n_pos": result.n_pos,
        "n_neg": result.n_neg,
        "undetermined_pivot": result.undetermined_pivot,
        "certified": result.certified,
        "pivot_transcript_sha256": digest,
        "pivots": list(result.pivots),
    }


def require_inertia(name: str, result: InertiaResult, expected: tuple[int, int]) -> None:
    if not result.certified:
        raise RuntimeError(f"{name}: pivot {result.undetermined_pivot} straddles zero")
    actual = (result.n_pos, result.n_neg)
    if actual != expected:
        raise RuntimeError(f"{name}: expected inertia {expected}, got {actual}")


def certify_case(c: int, N: int, prec: int, threshold_text: str) -> dict[str, object]:
    ctx.prec = prec
    threshold = arb(threshold_text)
    if not threshold > 0:
        raise ValueError("threshold must be a strictly positive Arb number")

    started = time.time()
    raw = build_cutoff_free_matrix(c, N, prec)
    sym = reflection_symmetric_enclosure(raw, N)
    even, odd = parity_blocks(sym, N)
    build_seconds = time.time() - started

    even_zero = certified_inertia(even)
    odd_zero = certified_inertia(odd)
    even_shift = certified_inertia(shifted(even, threshold))
    odd_shift = certified_inertia(shifted(odd, threshold))

    require_inertia("even at 0", even_zero, (N + 1, 0))
    require_inertia("odd at 0", odd_zero, (N, 0))
    require_inertia("even at threshold", even_shift, (N, 1))
    require_inertia("odd at threshold", odd_shift, (N, 0))

    return {
        "status": "PASS",
        "statement": (
            "0 < lambda_min(even) < threshold < lambda_min(odd), and exactly "
            "one full-matrix eigenvalue lies below threshold"
        ),
        "c": c,
        "N": N,
        "full_dimension": 2 * N + 1,
        "even_dimension": N + 1,
        "odd_dimension": N,
        "prec_bits": prec,
        "threshold": threshold_text,
        "build_seconds": round(build_seconds, 3),
        "even_unshifted": result_to_json(even_zero),
        "odd_unshifted": result_to_json(odd_zero),
        "even_shifted": result_to_json(even_shift),
        "odd_shifted": result_to_json(odd_shift),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--c", type=int, default=13)
    parser.add_argument("--N", type=int, default=20)
    parser.add_argument("--prec", type=int, default=900)
    parser.add_argument("--threshold", default="1e-38")
    parser.add_argument("--json-out", required=True)
    args = parser.parse_args()

    if args.c < 2 or args.N < 1 or args.prec < 128:
        parser.error("require c >= 2, N >= 1, prec >= 128")

    certificate = certify_case(args.c, args.N, args.prec, args.threshold)
    certificate.update(
        {
            "created_at": dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds"),
            "python_version": platform.python_version(),
            "python_flint_version": flint.__version__,
            "platform": platform.platform(),
            "source_formula_attribution": SOURCE_URL,
            "script_sha256": hashlib.sha256(open(__file__, "rb").read()).hexdigest(),
            "git_sha": os.environ.get("GITHUB_SHA"),
        }
    )

    os.makedirs(os.path.dirname(args.json_out) or ".", exist_ok=True)
    with open(args.json_out, "w", encoding="utf-8") as handle:
        json.dump(certificate, handle, indent=2)
        handle.write("\n")

    print(json.dumps({
        "status": certificate["status"],
        "c": args.c,
        "N": args.N,
        "threshold": args.threshold,
        "statement": certificate["statement"],
        "json_out": args.json_out,
    }, indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"CERTIFICATE FAILED: {exc}", file=sys.stderr)
        raise
