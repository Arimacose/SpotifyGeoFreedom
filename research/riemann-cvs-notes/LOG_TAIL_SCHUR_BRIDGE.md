# Logarithmic high-mode Schur bridge

## Status

This note records a proposed bridge from finite Galerkin parity certificates to
the infinite Fourier-coefficient operator.  The scalar Schur and no-crossing
inequalities have been formalized in Lean.  The operator estimates below are a
research program, not yet a theorem about the full Weil operator.

## 1. Target

Write the cutoff-free finite Weil matrix in the Fourier basis as

\[
\tau_L=W_{0,2}-W_R-W_p.
\]

For a projection `P_M` onto Fourier modes `|n| <= M`, split

\[
\tau_L=\begin{pmatrix}A_M&B_M^*\\B_M&C_M\end{pmatrix}.
\]

A sufficient infinite-Galerkin bridge is

\[
C_M-\mu I\succeq \gamma_M I,
\qquad \|B_M\|\le B_L,
\qquad \gamma_M\to\infty.
\]

Then the low-block Schur correction is bounded by

\[
\|B_M^*(C_M-\mu I)^{-1}B_M\|
\le \frac{B_L^2}{\gamma_M}.
\]

If this is smaller than a fixed fraction of the finite even/odd parity margin,
no parity crossing can occur when the high modes are restored.

## 2. Pole block is bounded finite rank

The explicit pole matrix has entries proportional to

\[
\frac{L^2-16\pi^2mn}
{(L^2+16\pi^2m^2)(L^2+16\pi^2n^2)}.
\]

Defining

\[
a_n=\frac{L}{L^2+16\pi^2n^2},
\qquad
b_n=\frac{4\pi n}{L^2+16\pi^2n^2},
\]

gives the exact rank-two factorization

\[
W_{0,2}=c_L\,(aa^*-bb^*).
\]

Both `a` and `b` lie in `ell^2(Z)`, so this block is bounded independently of
the Galerkin dimension.  It is not assumed positive.

## 3. Archimedean off-diagonal block as a Hilbert commutator

For `m != n`, the archimedean matrix has the Loewner form

\[
(W_R)_{mn}=\frac{S_m-S_n}{\pi(n-m)}.
\]

Let

\[
(Hx)_n=\sum_{m\ne n}\frac{x_m}{\pi(n-m)}
\]

be the normalized discrete Hilbert transform and `M_S` multiplication by the
bounded sequence `S`.  Then

\[
(W_R)_{\mathrm{off}}=HM_S-M_SH.
\]

The Fourier multiplier of `H` has modulus at most one, hence

\[
\|(W_R)_{\mathrm{off}}\|
\le 2\|S\|_\infty.
\]

A rigorous implementation still needs an explicit uniform bound for the
particular sequence `S_n` appearing in the cutoff-free formula.

## 4. Prime block as a sum of truncated translations

For a prime-power location `y=log q`, the matrix displayed by the finite CvS
formula is the matrix of the self-adjoint part of a truncated translation on the
interval of length `L`.  Since a truncated translation is a contraction,

\[
\|T_y+T_y^*\|\le2.
\]

Consequently the whole finite prime block should satisfy the dimension-free
bound

\[
\|W_p\|
\le 2\sum_{q\le c}\frac{\Lambda(q)}{\sqrt q}.
\]

The remaining proof obligation is to check the matrix-entry identification at
exact normalization, rather than merely up to an inessential factor.

## 5. Growing diagonal symbol

The diagonal archimedean entry is built from digamma and trigamma values at

\[
\frac14+\frac{i\pi n}{L}.
\]

The standard right-half-plane digamma asymptotic implies a bound of the form

\[
-(W_R)_{nn}
\ge \log(1+|n|)-C_L
\]

for all sufficiently large `|n|`, with an effective constant `C_L`.  The
trigamma and geometric-correction terms are lower order.

Combining the diagonal estimate with the bounded pole, prime, and commutator
pieces would yield

\[
C_M\succeq
\bigl(\log(1+M)-C_L-B_L\bigr)I.
\]

Thus one may take

\[
\gamma_M=\log(1+M)-C_L-B_L-\mu.
\]

## 6. Explicit no-crossing budget

Let `Delta` denote the finite low-block parity margin.  It is enough to choose
`M` so that

\[
\gamma_M>0,
\qquad
\frac{B_{L,+}^2}{\gamma_{M,+}}\le\frac\Delta4,
\qquad
\frac{B_{L,-}^2}{\gamma_{M,-}}\le\frac\Delta4.
\]

Equivalently, a multiplication-only sufficient condition is

\[
4B_{L,\pm}^2\le \Delta\,\gamma_{M,\pm}.
\]

The Lean module `LogTailNoCrossing.lean` verifies that these two quarter-margin
bounds preserve strict even/odd ordering.

The required `M` may be enormous because the prolate energies are exponentially
small.  That affects practicality, not existence: logarithmic growth of the
high-mode diagonal is still enough in principle if the remaining pieces are
uniformly bounded in the Galerkin dimension.

## 7. Relation to the prolate asymptotic chain

The low-mode analysis currently supplies the scale hierarchy

\[
\frac{E_+}{E_-}=O(\lambda^{-4}),
\qquad
\frac{\text{internal constrained gap}}{E_-}=\Theta(\lambda^8),
\qquad
\text{two-pole tail correction}=O(\lambda^{-7})
\]

under the stated fixed-index and Parseval inputs.  The infinite-Galerkin Schur
bridge is logically separate: it controls restoration of arbitrarily high
Fourier modes after a finite low block has been certified.

## 8. Remaining analytic lemmas

1. Prove a concrete uniform bound for `S_n` and hence for the discrete-Hilbert
   commutator.
2. Verify exactly that each prime matrix is the self-adjoint part of a truncated
   translation, including all normalization factors.
3. Give an explicit lower bound for the digamma diagonal symbol.
4. Bound the low/high coupling by the same dimension-free perturbation constant.
5. Combine the resulting complement gap with finite interval-certified parity
   margins and the prolate large-parameter asymptotics.

No Riemann-hypothesis claim follows until all five analytic inputs and the final
lowest-state convergence argument are completed.
