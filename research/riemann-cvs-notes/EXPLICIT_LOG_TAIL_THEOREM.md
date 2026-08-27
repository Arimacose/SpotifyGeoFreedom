# An explicit logarithmic high-mode theorem for the cutoff-free CvS matrix

## Status and scope

This note gives a self-contained analytic decomposition of the cutoff-free
finite/infinite Fourier matrix

\[
\tau_L=W_{0,2}-W_R-W_p,
\qquad L=\log c>0.
\]

It establishes the ingredients for an explicit finite-section convergence
bound at every fixed prime cutoff `c`.  It does **not** prove the Riemann
Hypothesis, large-parameter prolate/Weil coercivity, or the CCM ground-state
convergence statement.

The associated Lean modules verify the scalar Schur and no-crossing logic.  The
special-function estimates below remain conventional mathematical proofs rather
than a full Lean formalization.

---

## 1. Prime block: exact truncated-translation representation

Use the normalized Fourier basis of `L²(0,L)`,

\[
e_n(x)=L^{-1/2}e^{2\pi i n x/L}.
\]

For `0<y<L`, define the truncated translation

\[
(U_yf)(x)=\mathbf 1_{[0,L-y]}(x)f(x+y).
\]

It is a contraction.  A direct integration gives

\[
\langle e_n,U_ye_m\rangle=
\begin{cases}
(1-y/L)e^{2\pi i n y/L},&m=n,\\[1mm]
\displaystyle
\frac{e^{2\pi i n y/L}-e^{2\pi i m y/L}}
{2\pi i(m-n)},&m\ne n.
\end{cases}
\]

Consequently, the self-adjoint part `U_y+U_y*` has entries

\[
2(1-y/L)\cos(2\pi n y/L)
\]

on the diagonal, and

\[
\frac{\sin(2\pi m y/L)-\sin(2\pi n y/L)}
{\pi(n-m)}
\]

off the diagonal.  These are exactly the entries used for one prime-power event
in the finite CvS matrix.

Writing `y=log q` and

\[
w_q=\frac{\Lambda(q)}{\sqrt q},
\]

one obtains

\[
W_p=\sum_{q\le c}w_q(U_{\log q}+U_{\log q}^*),
\]

and therefore the dimension-free estimate

\[
\boxed{
\|W_p\|\le
2\sum_{q\le c}\frac{\Lambda(q)}{\sqrt q}.
}
\tag{1}
\]

---

## 2. Pole block: exact rank-two factorization

The pole block is

\[
(W_{0,2})_{mn}=
32L\sinh^2(L/4)
\frac{L^2-16\pi^2mn}
{(L^2+16\pi^2m^2)(L^2+16\pi^2n^2)}.
\]

Set

\[
a_n=\frac{L}{L^2+16\pi^2n^2},
\qquad
b_n=\frac{4\pi n}{L^2+16\pi^2n^2}.
\]

Then

\[
W_{0,2}=32L\sinh^2(L/4)(aa^*-bb^*).
\tag{2}
\]

Moreover,

\[
\|a\|^2+\|b\|^2
=
\sum_{n\in\mathbb Z}
\frac1{L^2+16\pi^2n^2}
=
\frac1{4L}\coth(L/4),
\]

using the standard partial-fraction expansion of `coth`.  Thus

\[
\boxed{
\|W_{0,2}\|\le4\sinh(L/2).
}
\tag{3}
\]

---

## 3. Archimedean off-diagonal block

For `m≠n`, the archimedean entries have Loewner form

\[
(W_R)_{mn}=\frac{S_m-S_n}{\pi(n-m)}.
\]

Let `H` denote the normalized discrete Hilbert transform

\[
(Hx)_n=\sum_{m\ne n}\frac{x_m}{\pi(n-m)}.
\]

Its Fourier multiplier has modulus at most one, hence `||H||=1`.  Therefore

\[
(W_R)_{\mathrm{off}}=M_SH-HM_S
\]

up to an inessential overall sign, and

\[
\|(W_R)_{\mathrm{off}}\|\le2\|S\|_\infty.
\tag{4}
\]

Put

\[
R_L=\frac{e^{-L/2}}{1-e^{-2L}}.
\]

For `a=1/4` and `y>0`,

\[
\operatorname{Im}\psi(a+iy)
=
\sum_{k\ge0}\frac{y}{(k+a)^2+y^2}
\le2+\frac\pi2.
\]

The geometric correction in `S_n` is at most `R_L`.  Hence

\[
\boxed{
\|S\|_\infty\le1+\frac\pi4+R_L
}
\tag{5}
\]

and

\[
\boxed{
\|(W_R)_{\mathrm{off}}\|
\le2\left(1+\frac\pi4+R_L\right).
}
\tag{6}
\]

---

## 4. Elementary lower bound for the digamma symbol

For `y≥1`, the defining series

\[
\operatorname{Re}\psi(1/4+iy)
=-\gamma+
\sum_{k\ge0}
\left(
\frac1{k+1}-
\frac{k+1/4}{(k+1/4)^2+y^2}
\right)
\]

gives the explicit bound

\[
\boxed{
\operatorname{Re}\psi(1/4+iy)
\ge\log y-C_\psi,
\qquad
C_\psi=\gamma+\frac45+\log\frac85.
}
\tag{7}
\]

Indeed, with `M=floor(y)`, the first `M` terms are at least
`H_M-1/2 ≥ log(y)-1/2`.  The remaining negative contribution is at most

\[
\frac3{10}+\log\frac85.
\]

For the geometric terms in the cutoff-free formula one has

\[
G_{CC}\le2R_L,
\qquad
G_{X1}\le2R_L,
\qquad
|G_{X2}|\le4R_L,
\]

and

\[
|\operatorname{Re}\psi'(1/4+iy)|
\le\psi'(1/4).
\]

Define

\[
\begin{aligned}
D_L={}&C_\psi+\psi(1/4)+\kappa_L+J_L
+8R_L+\frac{8R_L}{L}
+\frac{\psi'(1/4)}{2L}
+\log\frac{L}{\pi},
\end{aligned}
\tag{8}
\]

where `kappa_L` and `J_L` are the explicit cutoff constants in the CvS closed
form.  Then for every nonzero Fourier mode,

\[
\boxed{
-(W_R)_{nn}\ge\log|n|-D_L.
}
\tag{9}
\]

---

## 5. Bounded-perturbation representation

Let

\[
B_L=
4\sinh(L/2)
+2\left(1+\frac\pi4+R_L\right)
+2\sum_{q\le c}\frac{\Lambda(q)}{\sqrt q}.
\tag{10}
\]

Write the infinite Fourier matrix as

\[
\tau_L=D+K,
\]

where `D` is the diagonal matrix with entries `-(W_R)_{nn}` and `K` consists of
all remaining terms.  Equations (1), (3), and (6) yield

\[
\boxed{
\|K\|\le B_L.
}
\tag{11}
\]

If `Q_M` projects onto modes `|n|≥M+1`, then

\[
\boxed{
Q_M\tau_LQ_M
\succeq
\gamma_M Q_M,
\qquad
\gamma_M=\log(M+1)-D_L-B_L.
}
\tag{12}
\]

The diagonal part has no low/high coupling, so for `P_M=I-Q_M`,

\[
\boxed{
\|Q_M\tau_LP_M\|\le B_L.
}
\tag{13}
\]

In particular, `tau_L` is a bounded perturbation of a diagonal operator tending
to `+infinity`; its natural self-adjoint realization has compact resolvent.

---

## 6. Explicit finite-section error

Let `nu_M` be the lowest Rayleigh value of one parity compression to `P_M`, and
let `nu` be the corresponding full-parity lowest value.  Once `gamma_M>0`, the
normalized Schur estimate gives

\[
\nu_M-rac{2B_L^2}{\gamma_M}
\le\nu\le\nu_M,
\tag{14}
\]

provided the displayed lower target does not exceed the retained high floor
`gamma_M/2`.  The scalar statement and its division-free parity version are
formalized in `FiniteSectionConvergence.lean` and
`NormalizedBlockSchur.lean`.

For two parity sectors, a certified finite gap transfers to the full operator
whenever

\[
\nu_{M,-}-\nu_{M,+}
>
\frac{2B_{L,+}^2}{\gamma_{M,+}}
+
\frac{2B_{L,-}^2}{\gamma_{M,-}}.
\tag{15}
\]

---

## 7. Interpretation

This theorem closes the qualitative **finite-section convergence** problem at a
fixed cutoff: high Fourier modes eventually become coercive, and the truncation
error has an explicit Schur bound.  The constants are intentionally elementary
and very conservative.  Since the observed low parity margins are
exponentially small, the resulting Fourier cutoff needed for (15) may be
astronomically large.  Therefore this logarithmic bridge is not a replacement
for the sharper fixed-index prolate route, whose internal gap is of relative
order `lambda^8`.

The central unresolved analytic target remains a uniform coercivity/Schur bound
on the fixed prolate tail spaces that preserves the `lambda^-4` parity margin
with an error of order `lambda^-7` or smaller.
