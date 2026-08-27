import Mathlib

/-!
# Completing the square for a Schur-complement bound

This module formalizes the elementary inequality behind the low-block/high-block
reduction used in the CvS--prolate research line.  Analytically, one seeks a
positive lower bound `gap` for the high-mode complement and a coupling bound
`epsilon`.  Completing the square then limits the downward Schur correction to
`epsilon² / gap`.

The statements are scalar consequences of those analytic estimates.  They do
not assert that the estimates hold for the Weil quadratic form.
-/

namespace RiemannCvs.SchurQuadraticForm

/-- Division-free completion of the square.

The left side is exactly `(gap * t - epsilon * s)²`. -/
theorem squareCompletionMul
    (gap epsilon s t : ℝ) :
    0 ≤ gap * (gap * t ^ 2 - 2 * epsilon * s * t) +
      epsilon ^ 2 * s ^ 2 := by
  calc
    gap * (gap * t ^ 2 - 2 * epsilon * s * t) +
        epsilon ^ 2 * s ^ 2 =
      (gap * t - epsilon * s) ^ 2 := by ring
    _ ≥ 0 := sq_nonneg _

/-- Standard Schur correction bound obtained from the preceding
multiplication-only identity. -/
theorem squareCompletion
    (gap epsilon s t : ℝ)
    (hGap : 0 < gap) :
    -(epsilon ^ 2 / gap) * s ^ 2 ≤
      gap * t ^ 2 - 2 * epsilon * s * t := by
  have hMul := squareCompletionMul gap epsilon s t
  have hScaled :
      gap * (-(epsilon ^ 2 / gap) * s ^ 2) ≤
        gap * (gap * t ^ 2 - 2 * epsilon * s * t) := by
    have hCancel :
        gap * (-(epsilon ^ 2 / gap) * s ^ 2) =
          -(epsilon ^ 2) * s ^ 2 := by
      field_simp [ne_of_gt hGap]
      ring
    rw [hCancel]
    nlinarith
  exact (mul_le_mul_left hGap).mp hScaled

/-- Abstract quadratic-form version.

`high` is the high-complement contribution and `cross` is one copy of the
low/high cross term, so the total relative energy is
`low + 2 * cross + high`. -/
theorem schurFormLowerBound
    (low high cross gap epsilon s t : ℝ)
    (hGap : 0 < gap)
    (hHigh : gap * t ^ 2 ≤ high)
    (hCross : -epsilon * s * t ≤ cross) :
    low - (epsilon ^ 2 / gap) * s ^ 2 ≤
      low + 2 * cross + high := by
  have hSquare := squareCompletion gap epsilon s t hGap
  nlinarith

/-- Unit-low-vector specialization. -/
theorem schurUnitLowerBound
    (low high cross gap epsilon t total : ℝ)
    (hGap : 0 < gap)
    (hHigh : gap * t ^ 2 ≤ high)
    (hCross : -epsilon * t ≤ cross)
    (hTotal : total = low + 2 * cross + high) :
    low - epsilon ^ 2 / gap ≤ total := by
  rw [hTotal]
  have h := schurFormLowerBound
    low high cross gap epsilon 1 t hGap hHigh
  norm_num at h
  exact h hCross

/-- If an odd low block has baseline `oddBase`, the even sector has an upper
candidate `evenUpper`, and the Schur correction is strictly smaller than the
remaining margin, then the actual even minimum lies below every odd mixed
state represented by the supplied lower bound. -/
theorem parityFromSchurLowerBound
    (evenValue oddValue evenUpper oddBase gap epsilon : ℝ)
    (hGap : 0 < gap)
    (hEven : evenValue ≤ evenUpper)
    (hOdd : oddBase - epsilon ^ 2 / gap ≤ oddValue)
    (hMargin : evenUpper < oddBase - epsilon ^ 2 / gap) :
    evenValue < oddValue := by
  exact lt_of_le_of_lt hEven (lt_of_lt_of_le hMargin hOdd)

/-- Division-free sufficient margin for `parityFromSchurLowerBound`. -/
theorem divisionFreeParityMargin
    (evenUpper oddBase gap epsilon : ℝ)
    (hGap : 0 < gap)
    (hMargin : gap * (oddBase - evenUpper) > epsilon ^ 2) :
    evenUpper < oddBase - epsilon ^ 2 / gap := by
  have hScaled :
      epsilon ^ 2 / gap < oddBase - evenUpper := by
    exact (div_lt_iff₀ hGap).2 (by nlinarith [hMargin])
  nlinarith

end RiemannCvs.SchurQuadraticForm
