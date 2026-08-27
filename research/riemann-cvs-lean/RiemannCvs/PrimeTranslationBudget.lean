import Mathlib

/-!
# Weighted prime-translation budget

For a prime-power location, the finite CvS prime matrix is expected to be the
self-adjoint part of a truncated translation.  A truncated translation is a
contraction, so its quadratic contribution is bounded in absolute value by
twice the squared norm.  This module formalizes the finite weighted-sum step:
individual event bounds add with the von Mangoldt weights and do not depend on
the Galerkin dimension.

The matrix-entry identification and contraction estimate are analytic inputs,
not conclusions of this file.
-/

namespace RiemannCvs.PrimeTranslationBudget

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Nonnegative weighted event bounds sum to a dimension-free total bound. -/
theorem weightedPrimeEventBound
    (weight event : ι → ℝ) (normSq : ℝ)
    (hWeight : ∀ i, 0 ≤ weight i)
    (hEvent : ∀ i, |event i| ≤ 2 * normSq) :
    |∑ i, weight i * event i| ≤
      2 * (∑ i, weight i) * normSq := by
  calc
    |∑ i, weight i * event i|
        ≤ ∑ i, |weight i * event i| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, weight i * |event i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (hWeight i)]
    _ ≤ ∑ i, weight i * (2 * normSq) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hEvent i) (hWeight i)
    _ = 2 * (∑ i, weight i) * normSq := by
      rw [← Finset.sum_mul]
      ring

/-- Specialization when each event is already written as a symmetric
translation contribution bounded by `2 * normSq`. -/
theorem vonMangoldtTranslationBound
    (weight event : ι → ℝ) (normSq totalWeight : ℝ)
    (hWeight : ∀ i, 0 ≤ weight i)
    (hEvent : ∀ i, |event i| ≤ 2 * normSq)
    (hTotalWeight : totalWeight = ∑ i, weight i) :
    |∑ i, weight i * event i| ≤ 2 * totalWeight * normSq := by
  rw [hTotalWeight]
  exact weightedPrimeEventBound weight event normSq hWeight hEvent

end RiemannCvs.PrimeTranslationBudget
