import RiemannCvs.RadicalTailTransfer

/-!
# Near-identity tail maps

This file isolates the functional-analytic bridge suggested by the exterior
prolate-tail picture.  If a tail transform has the form `x ↦ x + e(x)` and the
remainder is small relative to `x`, then its squared norm is uniformly
comparable with the reference tail energy.  The available quartic prolate
parity margin therefore survives any remainder tending to zero (and, more
generally, any distortion growing slower than `λ⁴`).

No assertion about a concrete co-Poisson/Riemann-sum operator, a prolate tail,
or the Weil quadratic form is hidden here.  Such analytic statements enter only
as hypotheses.
-/

namespace RiemannCvs.NearIdentityTailMap

variable {E : Type*} [NormedAddCommGroup E]

/-- A relative additive error gives two-sided norm control. -/
theorem norm_add_relative_error_bounds
    (x e : E) (eps : ℝ)
    (heps_nonneg : 0 ≤ eps)
    (herr : ‖e‖ ≤ eps * ‖x‖) :
    (1 - eps) * ‖x‖ ≤ ‖x + e‖ ∧
      ‖x + e‖ ≤ (1 + eps) * ‖x‖ := by
  have hupper : ‖x + e‖ ≤ (1 + eps) * ‖x‖ := by
    calc
      ‖x + e‖ ≤ ‖x‖ + ‖e‖ := norm_add_le x e
      _ ≤ ‖x‖ + eps * ‖x‖ := add_le_add_left herr ‖x‖
      _ = (1 + eps) * ‖x‖ := by ring
  have htriangle : ‖x‖ ≤ ‖x + e‖ + ‖e‖ := by
    calc
      ‖x‖ = ‖(x + e) - e‖ := by simp
      _ ≤ ‖x + e‖ + ‖e‖ := norm_sub_le (x + e) e
  have hlower : (1 - eps) * ‖x‖ ≤ ‖x + e‖ := by
    nlinarith [norm_nonneg x]
  exact ⟨hlower, hupper⟩

/-- Squared-energy version of `norm_add_relative_error_bounds`. -/
theorem norm_sq_add_relative_error_bounds
    (x e : E) (eps : ℝ)
    (heps_nonneg : 0 ≤ eps)
    (heps_le_one : eps ≤ 1)
    (herr : ‖e‖ ≤ eps * ‖x‖) :
    (1 - eps) ^ 2 * ‖x‖ ^ 2 ≤ ‖x + e‖ ^ 2 ∧
      ‖x + e‖ ^ 2 ≤ (1 + eps) ^ 2 * ‖x‖ ^ 2 := by
  obtain ⟨hlower, hupper⟩ :=
    norm_add_relative_error_bounds x e eps heps_nonneg herr
  have hx_nonneg : 0 ≤ ‖x‖ := norm_nonneg x
  have hxe_nonneg : 0 ≤ ‖x + e‖ := norm_nonneg (x + e)
  have hleft_nonneg : 0 ≤ (1 - eps) * ‖x‖ :=
    mul_nonneg (sub_nonneg.mpr heps_le_one) hx_nonneg
  have hright_nonneg : 0 ≤ (1 + eps) * ‖x‖ :=
    mul_nonneg (by linarith) hx_nonneg
  constructor <;> nlinarith

/-- A near-identity tail map preserves the quartic prolate parity advantage.

The reference energies satisfy `λ⁴ E₊ ≤ C E₋`.  The transformed energies are
allowed the sharp squared-norm distortion factors `(1 ± eps)²`. -/
theorem quartic_parity_survives_near_identity
    (ePlus eMinus qPlus qMinus C lambda eps : ℝ)
    (hePlus : 0 ≤ ePlus)
    (heMinus : 0 < eMinus)
    (hlambda : 0 < lambda)
    (heps_nonneg : 0 ≤ eps)
    (heps_lt_one : eps < 1)
    (hqPlus : qPlus ≤ (1 + eps) ^ 2 * ePlus)
    (hqMinus : (1 - eps) ^ 2 * eMinus ≤ qMinus)
    (hQuarticRatio : lambda ^ 4 * ePlus ≤ C * eMinus)
    (hMargin : (1 + eps) ^ 2 * C < (1 - eps) ^ 2 * lambda ^ 4) :
    qPlus < qMinus := by
  exact RiemannCvs.RadicalTailTransfer.quarticMarginParityTransfer
    ePlus eMinus qPlus qMinus
    ((1 - eps) ^ 2) ((1 + eps) ^ 2) C lambda
    hePlus heMinus (sq_nonneg (1 + eps)) hlambda
    hqPlus hqMinus hQuarticRatio hMargin

/-- One-sided variant: a different relative error budget may be used in each
parity sector. -/
theorem quartic_parity_survives_asymmetric_tail_errors
    (ePlus eMinus qPlus qMinus C lambda epsPlus epsMinus : ℝ)
    (hePlus : 0 ≤ ePlus)
    (heMinus : 0 < eMinus)
    (hlambda : 0 < lambda)
    (hepsPlus_nonneg : 0 ≤ epsPlus)
    (hepsMinus_nonneg : 0 ≤ epsMinus)
    (hepsMinus_lt_one : epsMinus < 1)
    (hqPlus : qPlus ≤ (1 + epsPlus) ^ 2 * ePlus)
    (hqMinus : (1 - epsMinus) ^ 2 * eMinus ≤ qMinus)
    (hQuarticRatio : lambda ^ 4 * ePlus ≤ C * eMinus)
    (hMargin :
      (1 + epsPlus) ^ 2 * C <
        (1 - epsMinus) ^ 2 * lambda ^ 4) :
    qPlus < qMinus := by
  exact RiemannCvs.RadicalTailTransfer.quarticMarginParityTransfer
    ePlus eMinus qPlus qMinus
    ((1 - epsMinus) ^ 2) ((1 + epsPlus) ^ 2) C lambda
    hePlus heMinus (sq_nonneg (1 + epsPlus)) hlambda
    hqPlus hqMinus hQuarticRatio hMargin

end RiemannCvs.NearIdentityTailMap
