import Mathlib

/-!
# An explicit quartic tail margin from fixed Hermite radical vectors

For the first boundary-zero vectors in the additive Fourier `+1` and `-1`
classes, the common positive factors cancel and the pointwise amplitude ratio is
controlled by

`Real.sqrt 30 * plusPoly x / minusPoly x`.

This file proves an elementary non-asymptotic estimate for `x ≥ 2`.  It is the
scalar core of the fixed-Hermite large-parameter parity anchor described in
`FIXED_HERMITE_ANCHOR.md`.

The map `𝓔`, convergence of its Riemann sum, Poisson summation, integration of
the resulting estimate, and comparison with the Weil form are not hidden in
these statements.
-/

namespace RiemannCvs.HermiteTailAnchor

/-- Polynomial factor in the first Fourier `+1` boundary-zero Hermite vector. -/
def plusPoly (x : ℝ) : ℝ :=
  2 * Real.pi * x ^ 2 - 3

/-- Polynomial factor in the first Fourier `-1` boundary-zero Hermite vector. -/
def minusPoly (x : ℝ) : ℝ :=
  8 * Real.pi ^ 2 * x ^ 4 - 30 * Real.pi * x ^ 2 + 15

/-- A convenient lower bound for `pi * x²` on the tail range. -/
theorem twelve_le_pi_mul_sq
    (x : ℝ) (hx : 2 ≤ x) :
    12 ≤ Real.pi * x ^ 2 := by
  have hx2 : (4 : ℝ) ≤ x ^ 2 := by nlinarith
  calc
    (12 : ℝ) = 3 * 4 := by norm_num
    _ ≤ Real.pi * x ^ 2 :=
      mul_le_mul (le_of_lt Real.pi_gt_three) hx2
        (by norm_num) (le_of_lt Real.pi_pos)

/-- The `+1` polynomial is nonnegative for `x ≥ 2`. -/
theorem plusPoly_nonneg
    (x : ℝ) (hx : 2 ≤ x) :
    0 ≤ plusPoly x := by
  have h := twelve_le_pi_mul_sq x hx
  unfold plusPoly
  nlinarith

/-- Elementary upper bound for the `+1` polynomial. -/
theorem plusPoly_le_leading
    (x : ℝ) :
    plusPoly x ≤ 2 * Real.pi * x ^ 2 := by
  unfold plusPoly
  linarith

/-- The `-1` polynomial keeps at least two thirds of its leading term on
`[2,∞)`. -/
theorem minusPoly_leading_lower
    (x : ℝ) (hx : 2 ≤ x) :
    (16 / 3 : ℝ) * Real.pi ^ 2 * x ^ 4 ≤ minusPoly x := by
  have hprod := twelve_le_pi_mul_sq x hx
  have hpiSq : 0 ≤ Real.pi * x ^ 2 := by positivity
  have hbracket :
      0 ≤ (8 / 3 : ℝ) * Real.pi * x ^ 2 - 30 := by
    nlinarith
  have hnonneg :
      0 ≤ (Real.pi * x ^ 2) *
        ((8 / 3 : ℝ) * Real.pi * x ^ 2 - 30) :=
    mul_nonneg hpiSq hbracket
  unfold minusPoly
  nlinarith [hnonneg]

/-- In particular, the `-1` polynomial is positive on the tail range. -/
theorem minusPoly_pos
    (x : ℝ) (hx : 2 ≤ x) :
    0 < minusPoly x := by
  have hlower := minusPoly_leading_lower x hx
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hlead :
      0 < (16 / 3 : ℝ) * Real.pi ^ 2 * x ^ 4 := by positivity
  exact lt_of_lt_of_le hlead hlower

/-- The numerical constant needed in the amplitude comparison.  The proof uses
only `pi > 3` and `30 < (11/2)²`. -/
theorem six_sqrt_thirty_lt_eleven_pi :
    6 * Real.sqrt 30 < 11 * Real.pi := by
  have hsqrt0 : 0 ≤ Real.sqrt (30 : ℝ) := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt (30 : ℝ)) ^ 2 = 30 := by
    simpa using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 30)
  have hsqrt : Real.sqrt (30 : ℝ) < 11 / 2 := by
    nlinarith
  nlinarith [Real.pi_gt_three]

/-- Multiplication-only form of the pointwise Hermite comparison. -/
theorem scaled_core_ratio
    (x : ℝ) (hx : 2 ≤ x) :
    16 * x ^ 2 * Real.sqrt 30 * plusPoly x ≤
      11 * minusPoly x := by
  have hplus := plusPoly_le_leading x
  have hminus := minusPoly_leading_lower x hx
  have hsqrt0 : 0 ≤ Real.sqrt (30 : ℝ) := Real.sqrt_nonneg _
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hleftCoeff : 0 ≤ 16 * x ^ 2 * Real.sqrt 30 := by positivity
  have hleft := mul_le_mul_of_nonneg_left hplus hleftCoeff
  have hconst : 6 * Real.sqrt 30 ≤ 11 * Real.pi :=
    le_of_lt six_sqrt_thirty_lt_eleven_pi
  have hfactor :
      0 ≤ (16 / 3 : ℝ) * Real.pi * x ^ 4 := by positivity
  have hmiddle := mul_le_mul_of_nonneg_right hconst hfactor
  calc
    16 * x ^ 2 * Real.sqrt 30 * plusPoly x
        ≤ 16 * x ^ 2 * Real.sqrt 30 *
            (2 * Real.pi * x ^ 2) := hleft
    _ = 32 * Real.sqrt 30 * Real.pi * x ^ 4 := by ring
    _ ≤ (176 / 3 : ℝ) * Real.pi ^ 2 * x ^ 4 := by
      nlinarith [hmiddle]
    _ ≤ 11 * minusPoly x := by
      nlinarith

/-- Ratio form of `scaled_core_ratio`. -/
theorem core_ratio
    (x : ℝ) (hx : 2 ≤ x) :
    Real.sqrt 30 * plusPoly x ≤
      (11 / (16 * x ^ 2)) * minusPoly x := by
  have hscaled := scaled_core_ratio x hx
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hden : 0 < 16 * x ^ 2 := by positivity
  have hdiv :
      Real.sqrt 30 * plusPoly x ≤
        (11 * minusPoly x) / (16 * x ^ 2) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  calc
    Real.sqrt 30 * plusPoly x
        ≤ (11 * minusPoly x) / (16 * x ^ 2) := hdiv
    _ = (11 / (16 * x ^ 2)) * minusPoly x := by ring

/-- The source-norm normalization changes `(11/16)²` to `143/256`, which is
strictly below the convenient square `(3/4)²`. -/
theorem normalized_constant_margin :
    ((11 / 16 : ℝ) ^ 2) * (13 / 11) < (3 / 4 : ℝ) ^ 2 := by
  norm_num

/-- Exact rational identity behind the normalized margin. -/
theorem normalized_constant_exact :
    ((11 / 16 : ℝ) ^ 2) * (13 / 11) = 143 / 256 := by
  norm_num

/-- Once a pointwise normalized amplitude comparison has coefficient `3/4`,
squaring it produces the quartic mass coefficient `9/16`. -/
theorem square_three_quarters :
    (3 / 4 : ℝ) ^ 2 = 9 / 16 := by
  norm_num

end RiemannCvs.HermiteTailAnchor
