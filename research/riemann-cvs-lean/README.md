# Riemann CvS finite-dimensional reductions

This is an isolated Lean 4 verification package for finite-dimensional lemmas
arising in a research investigation of Connes–van Suijlekom/Connes–Consani–
Moscovici approximations to the Weil quadratic form.

## Verified scope

The package formalizes only finite-dimensional algebraic and order-theoretic
claims:

- rank-one prime-event transfer through a reduced resolvent;
- transfer through a linear functional;
- the von Mangoldt scalar cancellation used in a Laplace-weighted prime event;
- the canonical boundary-null combination in a two-dimensional plane;
- a displacement/resolvent identity;
- a constrained-ground spectral-weight certificate;
- the exact Rayleigh excess of the two-mode boundary-null vector;
- a gap-normalized ground-weight certificate depending only on the first two
  boundary coefficients.

The last item proves, under the stated spectral-decomposition hypotheses,

```text
1 - w ≤ c₀² / (c₀² + c₁²),
```

where `w` is the ground-state spectral weight of the constrained minimizer and
`c₀,c₁` are the boundary coefficients of the first two eigenvectors. The
absolute size of the possibly collapsing first spectral gap does not appear in
the final bound.

It does **not** formalize or claim the Riemann Hypothesis, convergence of the
finite Weil operators, the CCM simple-even hypothesis, decay of `c₀/c₁`, or any
asymptotic comparison between prolate leakage and the Weil quadratic form.

## Reproduce

```bash
lake exe cache get
lake build
lake env lean RiemannCvs/PrintAxioms.lean
```

CI additionally runs Lean's independent environment checker, rejects proof
placeholders, and runs an axiom audit allowing only `propext`,
`Classical.choice`, and `Quot.sound`.

## Pins

- Lean: `v4.33.0-rc2`
- Mathlib: `51e6992efd06126df61a496bebf8f49482a4e129`

These match the public `zeta-23-lean` formalization toolchain.
