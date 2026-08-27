# Exact constrained-prolate parity asymptotic

## Theorem

Let `nu_+(lambda)` and `nu_-(lambda)` denote the lowest eigenvalues of the
prolate concentration-defect operator after imposing the zero-integral boundary
condition in the Fourier `+1` and `-1` classes, respectively.  Under the standard
fixed-index prolate normalization

\[
c=2\pi\lambda^2,
\]

one has

\[
\boxed{
\frac{\nu_+(\lambda)}{\nu_-(\lambda)}
\sim
\frac{195}{1408\pi^2}\lambda^{-4}.
}
\tag{1}
\]

In particular, there exists `lambda_0` such that

\[
\nu_+(\lambda)<\nu_-(\lambda)
\qquad(\lambda\ge\lambda_0).
\tag{2}
\]

This is a theorem about the **pure boundary-constrained prolate model**.  It is
not yet a theorem about the true Weil quadratic form.

## Proof

### 1. Lowest constrained roots

In the Fourier `+1` class use fixed indices `(0,4,8,...)`; in the `-1` class use
`(2,6,10,...)`.  Write

\[
d_n(\lambda)=1-\chi_n(\lambda)
\]

for the concentration defects and

\[
r_n(\lambda)=
\left|\int_{-\lambda}^{\lambda}h_{n,\lambda}(x)\,dx\right|^2
\]

for the boundary residues.

The lowest constrained roots can be written

\[
\nu_+=d_0+\eta_+(d_4-d_0),
\qquad
\nu_-=d_2+\eta_-(d_6-d_2).
\tag{3}
\]

The exact secular identity and the Parseval/Fuchs estimate proved in
`PROLATE_TAIL_CORRECTION_THEOREM_V2.md` give

\[
\eta_+
=
\frac{r_0}{r_0+r_4}+O(\lambda^{-7}),
\]

and

\[
\eta_-
=
\frac{r_2}{r_2+r_6}+O(\lambda^{-7}).
\tag{4}
\]

### 2. Hermite residue limits

Fixed prolate modes converge to their Hermite limits.  With unitary Fourier
normalization, the squared integral/value ratios are

\[
r_4/r_0\longrightarrow3/8,
\qquad
r_6/r_2\longrightarrow5/8.
\]

Hence

\[
\eta_+\longrightarrow\frac1{1+3/8}=\frac8{11},
\qquad
\eta_-\longrightarrow
\frac{1/2}{1/2+5/16}=\frac8{13}.
\tag{5}
\]

### 3. Lower fixed modes are negligible

Fuchs' fixed-index asymptotic implies

\[
\frac{d_0}{d_4}=O(c^{-4}),
\qquad
\frac{d_2}{d_6}=O(c^{-4}).
\tag{6}
\]

Equations (3), (5), and (6) therefore yield

\[
\frac{\nu_+}{d_4}\longrightarrow\frac8{11},
\qquad
\frac{\nu_-}{d_6}\longrightarrow\frac8{13}.
\tag{7}
\]

### 4. Fixed-index defect ratio

The common leading Fuchs normalization cancels in the ratio, giving

\[
\frac{d_4}{d_6}
\sim
\frac{2^{12}/4!}{2^{18}/6!}c^{-2}
=
\frac{15}{32}c^{-2}.
\tag{8}
\]

Since `c=2*pi*lambda^2`,

\[
\frac{d_4}{d_6}
\sim
\frac{15}{128\pi^2}\lambda^{-4}.
\tag{9}
\]

Combining (7)--(9),

\[
\frac{\nu_+}{\nu_-}
\sim
\frac{8/11}{8/13}
\frac{15}{128\pi^2}\lambda^{-4}
=
\frac{195}{1408\pi^2}\lambda^{-4}.
\]

This proves (1), and (2) follows because the right-hand side tends to zero.

## Significance

Earlier two-mode calculations exhibited the same `lambda^-4` ratio but left
open whether the infinitely many higher prolate poles could change the leading
order.  The `O(lambda^-7)` secular-tail theorem rules that out.  Thus the pure
constrained-prolate parity mechanism is now closed at leading order.

The remaining main-chain problem is the transfer

\[
\text{constrained prolate ordering}
\quad\Longrightarrow\quad
\text{true Weil lowest-state ordering}.
\]

That transfer requires a uniform relative-form or Schur estimate on the actual
Weil tail spaces; it is not supplied by the theorem above.
