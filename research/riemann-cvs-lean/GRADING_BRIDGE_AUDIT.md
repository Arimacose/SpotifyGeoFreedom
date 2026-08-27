# Grading bridge audit: additive Fourier sign versus multiplicative inversion parity

## Purpose

The CCM simple-even hypothesis concerns the involution

\[
(Jg)(u)=g(u^{-1})
\]

on functions of the multiplicative variable.  The prolate/Hermite construction,
on the other hand, starts in the space of reflection-even functions on the
additive real line and then splits that space according to the eigenvalues
`+1` and `-1` of the additive Fourier transform.

These are distinct gradings before the map `𝓔` is applied.  They are not,
however, unrelated: Poisson summation intertwines them.

## Exact Poisson bridge

Let `f` be an even Schwartz function satisfying

\[
f(0)=\widehat f(0)=0,
\]

and define

\[
\mathcal E(f)(u)=u^{1/2}\sum_{n\geq1}f(nu),\qquad u>0.
\]

Poisson summation gives

\[
\sum_{n\in\mathbb Z}f(nu)
 =u^{-1}\sum_{m\in\mathbb Z}\widehat f(m/u).
\]

Evenness and the two vanishing conditions remove the zero terms, hence

\[
\mathcal E(f)(u)=\mathcal E(\widehat f)(u^{-1}),
\]

or equivalently

\[
\mathcal E(\widehat f)(u)=\mathcal E(f)(u^{-1}).
\tag{1}
\]

Consequently, if

\[
\widehat f=\varepsilon f,\qquad \varepsilon\in\{+1,-1\},
\]

then

\[
\boxed{\mathcal E(f)(u^{-1})=\varepsilon\mathcal E(f)(u).}
\tag{2}
\]

Thus the additive Fourier `+1` class maps to the inversion-even sector, while
the additive Fourier `-1` class maps to the inversion-odd sector.

## Consequence for the two Hermite families

The functions

\[
\psi^+_\ell
 =h_{4\ell}-\frac{h_{4\ell}(0)}{h_0(0)}h_0,
\]

and

\[
\psi^-_\ell
 =-h_{4\ell+2}
   +\frac{h_{4\ell+2}(0)}{h_2(0)}h_2
\]

belong to the even Schwartz space with
`f(0)=f̂(0)=0`.  Their additive Fourier eigenvalues are respectively `+1`
and `-1`.  Therefore

\[
\mathcal E(\psi^+_\ell)(u^{-1})
 =\mathcal E(\psi^+_\ell)(u),
\]

and

\[
\mathcal E(\psi^-_\ell)(u^{-1})
 =-\mathcal E(\psi^-_\ell)(u).
\]

Hence the previously studied `0,4` versus `2,6` comparison does compare the
correct multiplicative inversion sectors **after** applying `𝓔`.  It must not
be described as a direct comparison of reflection-even and reflection-odd
Hermite functions; all the source Hermite functions involved are
reflection-even.

## Finite-prolate defect

For a time-limited prolate vector the full Fourier relation is not exact.
Abstractly, suppose

\[
\widehat f=\varepsilon\chi f+r.
\]

Using (1),

\[
J\mathcal E(f)
 =\varepsilon\chi\mathcal E(f)+\mathcal E(r),
\]

and therefore

\[
\boxed{
J\mathcal E(f)-\varepsilon\mathcal E(f)
 =\varepsilon(\chi-1)\mathcal E(f)+\mathcal E(r).
}
\tag{3}
\]

The exact Hermite/radical model has `χ=1` and `r=0`.  In the finite prolate
model, equation (3) identifies the loss of exact inversion parity with the
Fourier concentration defect.  This is the correct location for the tail and
Schur-complement estimates developed elsewhere in this package.

## Formalization boundary

`RiemannCvs/FourierInversionBridge.lean` proves the linear-algebraic transfer
from an assumed intertwining identity to exact and approximate target parity.
It does not formalize Poisson summation or claim that a concrete prolate vector
satisfies the required analytic hypotheses.

## Updated research chain

The logically calibrated chain is now

\[
\begin{aligned}
&\text{Fourier }\pm\text{ prolate/Hermite classes}\\
&\xrightarrow{\text{Poisson}/\mathcal E}
  \text{multiplicative inversion }\pm\text{ classes}\\
&\xrightarrow{\text{radical truncation and tail control}}
  \text{Weil even/odd trial energies}\\
&\xrightarrow{\lambda^{-4}\text{ margin + error bounds}}
  \lambda_0^+<\lambda_0^-\\
&\xrightarrow{\text{Sylvester no crossing}}
  \text{simple-even ground state.}
\end{aligned}
\]

The main unresolved analytic assertion remains the uniform control of the Weil
form on the low-dimensional tail spaces, together with the complementary-block
Schur estimate.  The grading identification itself is no longer ambiguous.

## Primary references

- Connes–Consani–Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755,
  especially Sections 7–8.
- Connes–Consani–Moscovici, *Zeta zeros and prolate wave operators*,
  arXiv:2310.18423, especially Sections 3.5–3.6.
