import Mathlib

/-!
# Two-stage approximation geometry

The proposed analytic route compares three unit vectors:

* the true lowest Weil eigenvector `x`;
* the lowest vector `y` under the boundary constraint;
* the explicit prolate candidate `z` in the same constrained subspace.

This file proves the exact real-Hilbert-space geometry needed to compose the
two approximation steps. No spectral or asymptotic hypothesis is hidden in the
statements.
-/

namespace RiemannCvs.TwoStageApproximation

open scoped InnerProductSpace

variable {F : Type*}
variable [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Orthogonal-residual identity about an intermediate unit vector.

With `a = ⟪x,y⟫` and `b = ⟪y,z⟫`, subtracting the components along a unit
vector `y` leaves

`⟪x-a y, z-b y⟫ = ⟪x,z⟫ - a b`.
-/
theorem residualInnerIdentity
    (x y z : F) (a b : ℝ)
    (hy : ⟪y, y⟫_ℝ = 1)
    (ha : a = ⟪x, y⟫_ℝ)
    (hb : b = ⟪y, z⟫_ℝ) :
    ⟪x - a • y, z - b • y⟫_ℝ = ⟪x, z⟫_ℝ - a * b := by
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [← ha, ← hb, hy]
  ring

/-- Exact square norm of the residual after removing the component along a
unit intermediate vector. -/
theorem residualNormSq
    (x y : F) (a : ℝ)
    (hx : ‖x‖ = 1)
    (hy : ‖y‖ = 1)
    (ha : a = ⟪x, y⟫_ℝ) :
    ‖x - a • y‖ ^ 2 = 1 - a ^ 2 := by
  rw [norm_sub_sq_real, hx, norm_smul, hy, real_inner_smul_right]
  simp only [one_pow, mul_one, Real.norm_eq_abs]
  rw [← ha]
  nlinarith [sq_abs a]

/-- Sharp two-stage overlap lower bound in residual-norm form.

After signs/phases have been aligned so that the two intermediate overlaps are
`a` and `b`, Cauchy--Schwarz gives the only possible loss: the product of the
two orthogonal residual norms.
-/
theorem overlapLowerBoundByResiduals
    (x y z : F) (a b : ℝ)
    (hy : ⟪y, y⟫_ℝ = 1)
    (ha : a = ⟪x, y⟫_ℝ)
    (hb : b = ⟪y, z⟫_ℝ) :
    a * b - ‖x - a • y‖ * ‖z - b • y‖ ≤ ⟪x, z⟫_ℝ := by
  have hcs := abs_real_inner_le_norm (x - a • y) (z - b • y)
  have hlow :
      -(‖x - a • y‖ * ‖z - b • y‖) ≤
        ⟪x - a • y, z - b • y⟫_ℝ := by
    calc
      -(‖x - a • y‖ * ‖z - b • y‖)
          ≤ -|⟪x - a • y, z - b • y⟫_ℝ| := neg_le_neg hcs
      _ ≤ ⟪x - a • y, z - b • y⟫_ℝ := neg_abs_le _
  rw [residualInnerIdentity x y z a b hy ha hb] at hlow
  linarith

/-- Unit-vector specialization: the two residual squares are exactly the two
squared-overlap defects. -/
theorem unitOverlapLowerBoundByResiduals
    (x y z : F) (a b : ℝ)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1)
    (ha : a = ⟪x, y⟫_ℝ)
    (hb : b = ⟪y, z⟫_ℝ) :
    a * b - ‖x - a • y‖ * ‖z - b • y‖ ≤ ⟪x, z⟫_ℝ ∧
      ‖x - a • y‖ ^ 2 = 1 - a ^ 2 ∧
      ‖z - b • y‖ ^ 2 = 1 - b ^ 2 := by
  refine ⟨overlapLowerBoundByResiduals x y z a b ?_ ha hb, ?_, ?_⟩
  · simpa [real_inner_self_eq_norm_sq, hy]
  · exact residualNormSq x y a hx hy ha
  · exact residualNormSq z y b hz hy (by rw [real_inner_comm]; exact hb)

end RiemannCvs.TwoStageApproximation
