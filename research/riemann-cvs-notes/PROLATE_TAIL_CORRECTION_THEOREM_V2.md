# The first constrained prolate root has an `O(lambda^-7)` high-mode correction — corrected normalization-independent version

## Status

This note supersedes `PROLATE_TAIL_CORRECTION_THEOREM.md`.  It deliberately
uses only **ratios** of the fixed-index Fuchs constants, so it is independent of
conventions for the common leading normalization.

The result concerns the pure constrained prolate secular equation.  It does not
by itself transfer to the true Weil quadratic form and does not prove the
Riemann Hypothesis.

## 1. Setup

In one Fourier class, enumerate fixed prolate modes by

\[
(n_0,n_1,n_2,\ldots)=
\begin{cases}
(0,4,8,\ldots),&+1,\\
(2,6,10,\ldots),&-1.
\end{cases}
\]

Let

\[
d_j(\lambda)=1-\chi_{n_j}(\lambda),
\qquad
r_j(\lambda)=
\left|\int_{-\lambda}^{\lambda}h_{n_j,\lambda}(x)\,dx\right|^2.
\]

For the lowest constrained root `nu` in `(d_0,d_1)`, put

\[
g=d_1-d_0,
\qquad
\eta=\frac{\nu-d_0}{g},
\qquad
R=r_0+r_1,
\]

and

\[
H(\nu)=\sum_{j\ge2}\frac{r_j}{d_j-\nu}.
\]

## 2. Exact correction identity

The secular equation gives

\[
\boxed{
\frac{r_0}{r_0+r_1}-\eta
=
\frac{gH(\nu)\eta(1-\eta)}{r_0+r_1}.
}
\tag{1}
\]

Hence

\[
0\le\frac{r_0}{R}-\eta
\le
\frac{g}{4R}
\frac{\sum_{j\ge2}r_j}{d_2-\nu}.
\tag{2}
\]

## 3. Parseval residue budget

The interval integral functional is represented by the constant function on an
interval of length `2 lambda`.  Parseval therefore gives

\[
\sum_{j\ge0}r_j=2\lambda,
\qquad
\sum_{j\ge2}r_j\le2\lambda.
\tag{3}
\]

Thus

\[
0\le\frac{r_0}{R}-\eta
\le
\frac{\lambda g}{2R(d_2-\nu)}.
\tag{4}
\]

## 4. Fixed-index separation

Write the standard prolate bandwidth as

\[
c=2\pi\lambda^2.
\]

For fixed `n`, Fuchs' asymptotic can be written in the normalization-independent
form

\[
d_n(c)
\sim
C_F\,
\frac{2^{3n}}{n!}
 c^{n+1/2}e^{-2c},
\tag{5}
\]

where the positive common constant `C_F` does not depend on `n`.  Only its
cancellation in ratios is used below.  Therefore

\[
\frac{d_8}{d_4}
\sim
\frac{2^{24}/8!}{2^{12}/4!}c^4
=
\frac{256}{105}c^4,
\tag{6}
\]

and

\[
\frac{d_{10}}{d_6}
\sim
\frac{2^{30}/10!}{2^{18}/6!}c^4
=
\frac{256}{315}c^4.
\tag{7}
\]

Also `d_0/d_4 -> 0` and `d_2/d_6 -> 0`, so `g~d_1`, while
`d_2-nu~d_2` in the notation of Section 1.  Consequently

\[
\frac{g}{d_2-\nu}=O(c^{-4})=O(\lambda^{-8}).
\tag{8}
\]

Fixed-mode convergence to the Hermite functions gives

\[
R=r_0+r_1\longrightarrow R_\pm>0.
\tag{9}
\]

Substitution into (4) proves

\[
\boxed{
0\le
\frac{r_0}{r_0+r_1}-\eta
=O(\lambda^{-7}).
}
\tag{10}
\]

## 5. Explicit ratio-based upper constants

With the usual unitary Fourier normalization,

\[
R_+=\frac{11\sqrt2}{8},
\qquad
R_-=\frac{13\sqrt2}{16}.
\]

Using only `eta(1-eta)<=1/4` and the ratio limits (6)--(7), one obtains

\[
\limsup_{\lambda\to\infty}
\lambda^7
\left(\frac{r_0}{r_0+r_1}-\eta\right)
\le
\frac{105}{11264\sqrt2\,\pi^4}
\]

in the `+1` class, and

\[
\limsup_{\lambda\to\infty}
\lambda^7
\left(\frac{r_0}{r_0+r_1}-\eta\right)
\le
\frac{315}{6656\sqrt2\,\pi^4}
\]

in the `-1` class, under the stated bandwidth and Hermite normalizations.

## 6. Consequence

The pure constrained prolate parity signal is of relative order
`lambda^-4`, whereas the higher-pole secular correction is `O(lambda^-7)`.
Thus the higher fixed-index poles are asymptotically three powers too small to
erase the prolate parity ordering.  The unresolved step remains the transfer of
that ordering to the actual Weil quadratic form and its full lowest state.
