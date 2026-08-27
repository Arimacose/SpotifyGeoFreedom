# The first constrained prolate root has an `O(lambda^-7)` high-mode correction

## Status

This note upgrades the previously conjectural scale count to a rigorous
asymptotic consequence of three standard inputs already available in the
fixed-index prolate framework:

1. Fuchs' fixed-index concentration-defect asymptotic;
2. convergence of each fixed prolate mode to its Hermite limit;
3. Parseval for the interval integral functional.

The result concerns the **pure constrained prolate secular equation**.  It does
not by itself transfer to the true Weil quadratic form and does not prove the
Riemann Hypothesis.

---

## 1. Setup

In one Fourier eigenspace, enumerate the fixed-index prolate modes by

\[
(n_0,n_1,n_2,\ldots)=
\begin{cases}
(0,4,8,\ldots),&\text{Fourier eigenvalue }+1,\\
(2,6,10,\ldots),&\text{Fourier eigenvalue }-1.
\end{cases}
\]

Let

\[
d_j(\lambda)=1-\chi_{n_j}(\lambda)
\]

be their concentration defects and

\[
r_j(\lambda)=
\left|\int_{-\lambda}^{\lambda}
 h_{n_j,\lambda}(x)\,dx\right|^2
\]

be the squared boundary residues.  The lowest boundary-constrained secular
root `nu` lies in `(d_0,d_1)`.  Put

\[
g=d_1-d_0,
\qquad
\eta=\frac{\nu-d_0}{g},
\qquad
R=r_0+r_1.
\]

The higher-pole tail is

\[
H(\nu)=\sum_{j\ge2}\frac{r_j}{d_j-\nu}.
\]

---

## 2. Exact two-pole correction identity

The secular equation gives

\[
\boxed{
\frac{r_0}{r_0+r_1}-\eta
=
\frac{gH(\nu)\eta(1-\eta)}{r_0+r_1}.
}
\tag{1}
\]

In particular,

\[
0\le
\frac{r_0}{R}-\eta
\le
\frac{gH(\nu)}{4R}.
\tag{2}
\]

Since `d_j >= d_2` for `j>=2`,

\[
H(\nu)
\le
\frac{\sum_{j\ge2}r_j}{d_2-\nu}.
\tag{3}
\]

---

## 3. Parseval supplies only linear residue growth

The boundary functional is integration over an interval of length `2 lambda`.
For a complete orthonormal prolate basis, Parseval gives

\[
\sum_{j\ge0}r_j=2\lambda.
\tag{4}
\]

Therefore

\[
\sum_{j\ge2}r_j\le2\lambda.
\tag{5}
\]

Combining (2)--(5),

\[
0\le
\frac{r_0}{R}-\eta
\le
\frac{\lambda g}{2R(d_2-\nu)}.
\tag{6}
\]

---

## 4. Fixed-index defect separation

Write the standard prolate bandwidth as

\[
c=2\pi\lambda^2.
\]

Fuchs' fixed-index asymptotic has the form

\[
d_n(c)
\sim
4\sqrt\pi\,
\frac{2^{3n}}{n!}
 c^{n+1/2}e^{-2c}.
\tag{7}
\]

Consequently,

\[
\frac{d_8}{d_4}
\sim
\frac{256}{105}c^4,
\qquad
\frac{d_{10}}{d_6}
\sim
\frac{256}{315}c^4.
\tag{8}
\]

Also `d_0/d_4 -> 0` and `d_2/d_6 -> 0`, so `g~d_1`, while
`d_2-nu~d_2` in the notation of Section 1.  Thus

\[
\frac{g}{d_2-\nu}=O(c^{-4})=O(\lambda^{-8}).
\tag{9}
\]

Fixed-mode convergence to the Hermite functions implies

\[
R=r_0+r_1\longrightarrow R_\pm>0.
\tag{10}
\]

Substituting (9) and (10) into (6) proves

\[
\boxed{
0\le
\frac{r_0}{r_0+r_1}-\eta
=O(\lambda^{-7}).
}
\tag{11}
\]

---

## 5. Explicit asymptotic constants

With the usual unitary Fourier normalization, the Hermite residue limits are

\[
R_+=\sqrt2\left(1+\frac38\right)
=\frac{11\sqrt2}{8},
\]

and

\[
R_-=\sqrt2\left(\frac12+\frac5{16}\right)
=\frac{13\sqrt2}{16}.
\]

Using only `eta(1-eta)<=1/4`, equations (6) and (8) yield the asymptotic upper
constants

\[
\limsup_{\lambda\to\infty}
\lambda^7
\left(
\frac{r_0}{r_0+r_1}-\eta
\right)
\le
\frac{105}{11264\sqrt2\,\pi^4}
\]

in the `+1` class, and

\[
\limsup_{\lambda\to\infty}
\lambda^7
\left(
\frac{r_0}{r_0+r_1}-\eta
\right)
\le
\frac{315}{6656\sqrt2\,\pi^4}
\]

in the `-1` class, provided the standard asymptotic normalizations above are
used.

The constants are not expected to be sharp; the important feature is the power
`lambda^-7`.

---

## 6. Consequence for the parity program

The pure prolate constrained energies satisfy

\[
\frac{E_+}{E_-}=\Theta(\lambda^{-4}).
\]

The high-mode secular correction is smaller by three powers:

\[
\lambda^{-7}=o(\lambda^{-4}).
\]

Therefore higher fixed-index prolate poles cannot erase the leading parity
margin.  The remaining hard step is not the secular tail: it is the transfer of
this constrained-prolate ordering to the actual Weil quadratic form and its
infinite-dimensional lowest state.
