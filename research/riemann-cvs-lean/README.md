# Riemann CvS finite-dimensional reductions

This is an isolated Lean 4 verification package for finite-dimensional lemmas
arising in a research investigation of Connes–van Suijlekom/Connes–Consani–
Moscovici approximations to the Weil quadratic form.

## Verified scope

The package formalizes only finite-dimensional algebraic and order-theoretic
claims:

- rank-one event transfer through a reduced resolvent;
- transfer through a linear functional;
- the von Mangoldt scalar cancellation used in a Laplace-weighted prime event;
- the canonical boundary-null combination in a two-dimensional plane;
- a displacement/resolvent identity;
- a constrained-ground spectral-weight certificate.

It does **not** formalize or claim the Riemann Hypothesis, convergence of the
finite Weil operators, the CCM simple-even hypothesis, or any asymptotic
estimate for the constrained Rayleigh excess.

## Reproduce

```bash
lake exe cache get
lake build
lake env lean RiemannCvs/PrintAxioms.lean
```

CI additionally runs Lean's independent environment checker and an axiom audit
allowing only `propext`, `Classical.choice`, and `Quot.sound`.

## Pins

- Lean: `v4.33.0-rc2`
- Mathlib: `51e6992efd06126df61a496bebf8f49482a4e129`

These match the public `zeta-23-lean` formalization toolchain.
