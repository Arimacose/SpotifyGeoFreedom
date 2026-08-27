# Fixed-Hermite large-parameter anchor for the parity problem

## 1. Motivation

The prolate candidate is indispensable for the convergence-to-`Xi` part of the
CCM strategy, but it is not logically necessary for every part of the
`simple-even` problem.  For a large-parameter parity anchor one may instead use
fixed Hermite radical vectors.  They have three advantages:

1. their additive Fourier grading is exact;
2. Poisson summation sends this grading to exact multiplicative inversion
   parity under the map `E`;
3. their Gaussian tails admit elementary pointwise comparison estimates with
   explicit constants.

This separates the tasks:

- fixed Hermite radical vectors provide a candidate large-`lambda` parity
  anchor;
- prolate vectors continue to provide the candidate converging to the Riemann
  `Xi` function.

The remaining nontrivial bridge is a comparison of the Weil quadratic form on
the corresponding exterior-tail directions.

## 2. The first two Fourier classes

Use the normalized Hermite functions for the Fourier convention

\[
\widehat f(y)=\int_{\mathbb R}f(x)e^{2\pi ixy}\,dx.
\]

The first boundary-zero vectors in the two Fourier classes are

\[
\psi_+(x)=h_4(x)-\sqrt{\frac38}\,h_0(x),
\]

and

\[
\psi_-(x)=-h_6(x)+\sqrt{\frac58}\,h_2(x).
\]

They satisfy

\[
\widehat{\psi_+}=\psi_+,
\qquad
\widehat{\psi_-}=-\psi_-,
\]

as well as

\[
\psi_\pm(0)=\widehat{\psi_\pm}(0)=0.
\]

Their squared norms are

\[
\|\psi_+\|_2^2=\frac{11}{8},
\qquad
\|\psi_-\|_2^2=\frac{13}{8}.
\tag{1}
\]

The explicit formulas are

\[
\psi_+(x)
 =\frac{2\,2^{3/4}\sqrt3\,\pi}{3}
   x^2(2\pi x^2-3)e^{-\pi x^2},
\tag{2}
\]

and

\[
\psi_-(x)
 =-\frac{2\,2^{1/4}\sqrt5\,\pi}{15}
   x^2(8\pi^2x^4-30\pi x^2+15)e^{-\pi x^2}.
\tag{3}
\]

The ratio of the two positive prefactors in (2)--(3) is `sqrt(30)`.

## 3. An elementary pointwise quartic comparison

For `x >= 2`,

\[
0\le 2\pi x^2-3\le 2\pi x^2.
\tag{4}
\]

Moreover, using only `pi > 3` and `x^2 >= 4`,

\[
8\pi^2x^4-30\pi x^2+15
 \ge \frac{16}{3}\pi^2x^4.
\tag{5}
\]

Indeed,

\[
\begin{aligned}
&8\pi^2x^4-30\pi x^2+15
 -\frac{16}{3}\pi^2x^4\\
&\qquad
 =\pi x^2\left(\frac83\pi x^2-30\right)+15\ge0.
\end{aligned}
\]

The numerical constant is controlled without a decimal approximation:

\[
6\sqrt{30}<33<11\pi.
\tag{6}
\]

Combining (2)--(6) gives, for every `x >= 2`,

\[
0\le \psi_+(x)
 \le \frac{11}{16x^2}\bigl(-\psi_-(x)\bigr).
\tag{7}
\]

The signs in (7) are important: there is no cancellation when the values are
summed over positive integer dilations.

## 4. Transfer through the map `E`

Define

\[
\mathcal E(f)(u)=u^{1/2}\sum_{n\ge1}f(nu).
\]

For `u >= 2`, every argument `nu` lies in the range where (7) holds.  Since all
terms in the `+` series are nonnegative and all terms in the `-` series are
nonpositive,

\[
0\le \mathcal E(\psi_+)(u)
 \le \frac{11}{16u^2}
   \bigl(-\mathcal E(\psi_-)(u)\bigr).
\tag{8}
\]

Normalize the source vectors by

\[
\widetilde\psi_+=\sqrt{\frac8{11}}\,\psi_+,
\qquad
\widetilde\psi_-=\sqrt{\frac8{13}}\,\psi_-.
\]

Since

\[
\left(\frac{11}{16}\right)^2\frac{13}{11}
 =\frac{143}{256}<\frac9{16},
\]

(8) yields the clean estimate

\[
\boxed{
|\mathcal E(\widetilde\psi_+)(u)|
 \le \frac{3}{4u^2}
 |\mathcal E(\widetilde\psi_-)(u)|,
 \qquad u\ge2.
}
\tag{9}
\]

Squaring and integrating against `d*u = du/u` gives, for every `lambda >= 2`,

\[
\int_\lambda^\infty
 |\mathcal E(\widetilde\psi_+)(u)|^2\,d^*u
 \le
 \frac{9}{16\lambda^4}
 \int_\lambda^\infty
 |\mathcal E(\widetilde\psi_-)(u)|^2\,d^*u.
\tag{10}
\]

Poisson summation gives exact multiplicative inversion parity,

\[
\mathcal E(\widetilde\psi_+)(u^{-1})
 =\mathcal E(\widetilde\psi_+)(u),
\]

\[
\mathcal E(\widetilde\psi_-)(u^{-1})
 =-\mathcal E(\widetilde\psi_-)(u).
\]

Therefore the same ratio holds for the complete exterior of the symmetric
multiplicative interval:

\[
\boxed{
\frac{
 \|1_{(0,\lambda^{-1})\cup(\lambda,\infty)}
   \mathcal E(\widetilde\psi_+)\|_2^2
}{
 \|1_{(0,\lambda^{-1})\cup(\lambda,\infty)}
   \mathcal E(\widetilde\psi_-)\|_2^2
}
 \le \frac{9}{16\lambda^4},
 \qquad \lambda\ge2.
}
\tag{11}
\]

This is an explicit non-asymptotic quartic separation for exact inversion
parity vectors.

## 5. Relation to the Weil form

The range of `E` on the boundary-zero Schwartz space lies in the radical of the
full Weil form.  If

\[
F_\pm=\mathcal E(\widetilde\psi_\pm)
 =g_{\pm,\lambda}+t_{\pm,\lambda},
\]

where `g` is retained on `[lambda^-1, lambda]` and `t` is the exterior tail,
then the radical identity gives

\[
QW(g_{\pm,\lambda},g_{\pm,\lambda})
 =QW(t_{\pm,\lambda},t_{\pm,\lambda}).
\tag{12}
\]

The retained vectors have exact opposite inversion parity.  Thus (11) supplies
an explicit parity margin at the level of the reference tail norm.  To turn it
into an ordering of the actual Weil Rayleigh values, it is enough to prove a
uniform two-direction comparison such as

\[
QW(t_{+,\lambda})\le \beta\|t_{+,\lambda}\|_2^2,
\qquad
QW(t_{-,\lambda})\ge \alpha\|t_{-,\lambda}\|_2^2,
\tag{13}
\]

with `alpha > 0` and `beta/alpha = o(lambda^4)`; fixed positive constants would
already suffice.

The odd-sector trial value is still only an upper bound for the odd ground
state.  A complete simple-even proof additionally needs a lower bound there,
for example through a Temple estimate or a Schur-complement bound on the
orthogonal complement.

## 6. Research significance

Equation (11) removes two avoidable sources of uncertainty from the
large-parameter parity anchor:

- it uses exact Fourier/inversion parity, not approximate finite-prolate parity;
- it is non-asymptotic and elementary once the explicit Hermite formulas are
  inserted.

It does not prove the needed Weil-form comparison (13), and therefore does not
prove simple-even or RH.  It does, however, reduce the large-parameter parity
signal to a concrete explicit margin:

\[
\boxed{\text{even exterior mass}/\text{odd exterior mass}
       \le 9/(16\lambda^4).}
\]

This fixed-Hermite anchor can be pursued in parallel with the prolate candidate
used for convergence to `Xi`.
