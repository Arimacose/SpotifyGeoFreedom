import Mathlib

/-!
# Exact geometry of prolate leakage combinations

This file records the Hilbert-space identities behind the fixed-index prolate
parity comparison.  In the intended application, a unit prolate mode is split
into its Fourier transform inside the time window and its outside leakage.
Distinct modes have orthogonal retained parts and orthogonal total Fourier
transforms; hence their outside leakages are orthogonal as well.

Consequently, the leakage of a boundary-zero combination is an exact weighted
average of the individual concentration defects.  The special-function
asymptotics and the identification of concrete prolate modes are external
analytic inputs, not hidden in these theorems.
-/

namespace RiemannCvs.ProlateLeakage

open scoped InnerProductSpace

variable {F : Type*}
variable [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Pythagoras for a retained part and an orthogonal leakage part, normalized so
that the total mode has norm one. -/
theorem leakageNormSq
    (p r f : F)
    (hdecomp : f = p + r)
    (horth : ⟪p, r⟫_ℝ = 0)
    (hf : ‖f‖ = 1) :
    ‖r‖ ^ 2 = 1 - ‖p‖ ^ 2 := by
  have hpyth : ‖f‖ ^ 2 = ‖p‖ ^ 2 + ‖r‖ ^ 2 := by
    rw [hdecomp, norm_add_sq_real, horth]
    ring
  rw [hf] at hpyth
  nlinarith

/-- Orthogonality of total modes and of all retained/cross terms forces
orthogonality of the corresponding leakage tails. -/
theorem leakageOrthogonal
    (f₀ f₁ p₀ p₁ r₀ r₁ : F)
    (hf₀ : f₀ = p₀ + r₀)
    (hf₁ : f₁ = p₁ + r₁)
    (htotal : ⟪f₀, f₁⟫_ℝ = 0)
    (hpp : ⟪p₀, p₁⟫_ℝ = 0)
    (hpr : ⟪p₀, r₁⟫_ℝ = 0)
    (hrp : ⟪r₀, p₁⟫_ℝ = 0) :
    ⟪r₀, r₁⟫_ℝ = 0 := by
  rw [hf₀, hf₁, inner_add_left, inner_add_right, inner_add_right] at htotal
  rw [hpp, hpr, hrp] at htotal
  simpa using htotal

/-- The squared norm of a linear combination of orthogonal leakage vectors is
the sum of the two squared contributions. -/
theorem orthogonalCombinationNormSq
    (r₀ r₁ : F) (a b : ℝ)
    (horth : ⟪r₀, r₁⟫_ℝ = 0) :
    ‖a • r₀ + b • r₁‖ ^ 2 =
      a ^ 2 * ‖r₀‖ ^ 2 + b ^ 2 * ‖r₁‖ ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul,
    real_inner_smul_left, real_inner_smul_right, horth]
  simp only [Real.norm_eq_abs, mul_zero, add_zero]
  ring_nf
  rw [sq_abs a, sq_abs b]
  ring

/-- Exact leakage energy of the boundary-zero combination
`a rHigh - b rLow`. -/
theorem boundaryCombinationNormSq
    (rLow rHigh : F) (a b dLow dHigh : ℝ)
    (horth : ⟪rHigh, rLow⟫_ℝ = 0)
    (hLow : ‖rLow‖ ^ 2 = dLow)
    (hHigh : ‖rHigh‖ ^ 2 = dHigh) :
    ‖a • rHigh - b • rLow‖ ^ 2 =
      a ^ 2 * dHigh + b ^ 2 * dLow := by
  have h := orthogonalCombinationNormSq rHigh rLow a (-b) horth
  simpa [sub_eq_add_neg, hLow, hHigh] using h

/-- Dividing the exact leakage of a boundary-zero combination by its squared
coefficient norm gives the exact normalized candidate energy. -/
theorem normalizedBoundaryLeakage
    (rLow rHigh : F) (a b dLow dHigh : ℝ)
    (_hden : a ^ 2 + b ^ 2 ≠ 0)
    (horth : ⟪rHigh, rLow⟫_ℝ = 0)
    (hLow : ‖rLow‖ ^ 2 = dLow)
    (hHigh : ‖rHigh‖ ^ 2 = dHigh) :
    ‖a • rHigh - b • rLow‖ ^ 2 / (a ^ 2 + b ^ 2) =
      (a ^ 2 * dHigh + b ^ 2 * dLow) / (a ^ 2 + b ^ 2) := by
  rw [boundaryCombinationNormSq rLow rHigh a b dLow dHigh horth hLow hHigh]

/-- Scalar form useful after the exact Hilbert-space calculation: if the lower
mode defect is bounded by `alpha` times the higher mode defect, then the
normalized boundary-zero candidate is bounded by the corresponding weighted
coefficient. -/
theorem normalizedLeakageUpperBound
    (aSq bSq dLow dHigh alpha energy : ℝ)
    (_haSq : 0 ≤ aSq)
    (hbSq : 0 ≤ bSq)
    (hden : 0 < aSq + bSq)
    (_hdHigh : 0 ≤ dHigh)
    (hdLow : dLow ≤ alpha * dHigh)
    (henergy : energy = (aSq * dHigh + bSq * dLow) / (aSq + bSq)) :
    energy ≤ ((aSq + bSq * alpha) / (aSq + bSq)) * dHigh := by
  rw [henergy]
  have hscaled : bSq * dLow ≤ bSq * (alpha * dHigh) :=
    mul_le_mul_of_nonneg_left hdLow hbSq
  have hnum :
      aSq * dHigh + bSq * dLow ≤ (aSq + bSq * alpha) * dHigh := by
    nlinarith
  calc
    (aSq * dHigh + bSq * dLow) / (aSq + bSq)
        ≤ ((aSq + bSq * alpha) * dHigh) / (aSq + bSq) :=
          (div_le_div_iff_of_pos_right hden).2 hnum
    _ = ((aSq + bSq * alpha) / (aSq + bSq)) * dHigh := by ring

/-- Matching lower bound when the lower-mode defect is nonnegative. -/
theorem normalizedLeakageLowerBound
    (aSq bSq dLow dHigh energy : ℝ)
    (_haSq : 0 ≤ aSq)
    (hbSq : 0 ≤ bSq)
    (hden : 0 < aSq + bSq)
    (hdLow : 0 ≤ dLow)
    (henergy : energy = (aSq * dHigh + bSq * dLow) / (aSq + bSq)) :
    (aSq / (aSq + bSq)) * dHigh ≤ energy := by
  rw [henergy]
  have hnonneg : 0 ≤ bSq * dLow := mul_nonneg hbSq hdLow
  have hnum : aSq * dHigh ≤ aSq * dHigh + bSq * dLow := by
    nlinarith
  calc
    (aSq / (aSq + bSq)) * dHigh
        = (aSq * dHigh) / (aSq + bSq) := by ring
    _ ≤ (aSq * dHigh + bSq * dLow) / (aSq + bSq) :=
      (div_le_div_iff_of_pos_right hden).2 hnum

end RiemannCvs.ProlateLeakage
