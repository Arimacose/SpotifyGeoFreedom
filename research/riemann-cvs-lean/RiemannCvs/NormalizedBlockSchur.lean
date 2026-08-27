import Mathlib
import RiemannCvs.SchurQuadraticForm

/-!
# Normalized two-block Schur lower bounds

A subtlety in passing from a low-block Schur estimate to a lower bound for the
whole normalized vector is that a vector may lie entirely in the high block.
Keeping half of the high coercivity term resolves this: completing the square
with the other half costs `2 * epsilon² / gap`, while the retained half supplies
`gap / 2` on the high component.

This is the scalar certificate used by the finite Arb block experiment.  The
operator norm and complement-gap estimates remain external inputs.
-/

namespace RiemannCvs.NormalizedBlockSchur

/-- General normalized two-block lower certificate. -/
theorem normalizedBlockLowerBound
    (target low high cross lowLevel gap epsilon s t total : ℝ)
    (hGap : 0 < gap)
    (hLow : lowLevel * s ^ 2 ≤ low)
    (hHigh : gap * t ^ 2 ≤ high)
    (hCross : -epsilon * s * t ≤ cross)
    (hNorm : s ^ 2 + t ^ 2 = 1)
    (hTargetLow : target ≤ lowLevel - 2 * epsilon ^ 2 / gap)
    (hTargetHigh : target ≤ gap / 2)
    (hTotal : total = low + 2 * cross + high) :
    target ≤ total := by
  have hHalfGap : 0 < gap / 2 := by linarith
  have hSquare :=
    RiemannCvs.SchurQuadraticForm.squareCompletion
      (gap / 2) epsilon s t hHalfGap
  have hDivision :
      epsilon ^ 2 / (gap / 2) = 2 * epsilon ^ 2 / gap := by
    field_simp [ne_of_gt hGap]
    ring
  rw [hDivision] at hSquare
  rw [hTotal]
  nlinarith

/-- The familiar explicit lower bound, provided it is no larger than the
retained high-block floor `gap / 2`. -/
theorem normalizedBlockSchurBound
    (low high cross lowLevel gap epsilon s t total : ℝ)
    (hGap : 0 < gap)
    (hLow : lowLevel * s ^ 2 ≤ low)
    (hHigh : gap * t ^ 2 ≤ high)
    (hCross : -epsilon * s * t ≤ cross)
    (hNorm : s ^ 2 + t ^ 2 = 1)
    (hFloor : lowLevel - 2 * epsilon ^ 2 / gap ≤ gap / 2)
    (hTotal : total = low + 2 * cross + high) :
    lowLevel - 2 * epsilon ^ 2 / gap ≤ total := by
  exact normalizedBlockLowerBound
    (lowLevel - 2 * epsilon ^ 2 / gap)
    low high cross lowLevel gap epsilon s t total
    hGap hLow hHigh hCross hNorm le_rfl hFloor hTotal

/-- Division-free sufficient condition for a target lower bound. -/
theorem normalizedBlockTargetOfProductBudgets
    (target low high cross lowLevel gap epsilon s t total : ℝ)
    (hGap : 0 < gap)
    (hLow : lowLevel * s ^ 2 ≤ low)
    (hHigh : gap * t ^ 2 ≤ high)
    (hCross : -epsilon * s * t ≤ cross)
    (hNorm : s ^ 2 + t ^ 2 = 1)
    (hLowBudget : gap * (lowLevel - target) ≥ 2 * epsilon ^ 2)
    (hHighBudget : 2 * target ≤ gap)
    (hTotal : total = low + 2 * cross + high) :
    target ≤ total := by
  have hTargetLow : target ≤ lowLevel - 2 * epsilon ^ 2 / gap := by
    have hDiv : 2 * epsilon ^ 2 / gap ≤ lowLevel - target := by
      exact (div_le_iff₀ hGap).2 (by nlinarith [hLowBudget])
    nlinarith
  have hTargetHigh : target ≤ gap / 2 := by nlinarith
  exact normalizedBlockLowerBound
    target low high cross lowLevel gap epsilon s t total
    hGap hLow hHigh hCross hNorm
    hTargetLow hTargetHigh hTotal

end RiemannCvs.NormalizedBlockSchur
