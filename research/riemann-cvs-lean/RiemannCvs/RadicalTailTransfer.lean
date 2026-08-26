import Mathlib

/-!
# Radical splitting and conditioned tail transfer

This file formalizes the finite-dimensional algebra behind a proposed bridge
from prolate concentration leakage to the truncated Weil quadratic form.

The motivating picture is:

* a global vector `F` lies in the radical of a symmetric bilinear form;
* `F = g + r`, where `g` is the retained interval part and `r` is its tail;
* the retained energy equals the tail energy exactly;
* on the two parity-relevant tail directions, comparison with a positive
  reference leakage norm need only have condition number `o(λ^4)` because the
  pure prolate parity ratio is already of order `λ⁻⁴`.

The analytic assertions needed to instantiate these hypotheses for the Weil
form are deliberately not hidden in the statements below.
-/

namespace RiemannCvs.RadicalTailTransfer

section RadicalSplit

variable {V : Type*} [AddCommGroup V]

/-- If `F = g + r` lies in the left radical of a symmetric additive form, then
its retained part and its tail have exactly the same quadratic energy.

Only the four identities actually used in the proof are assumed; no continuity,
positivity, or finite dimensionality is required. -/
theorem radicalSplitEnergyIdentity
    (B : V → V → ℝ) (F g r : V)
    (hF : F = g + r)
    (haddLeft : ∀ x y z, B (x + y) z = B x z + B y z)
    (hsymm : ∀ x y, B x y = B y x)
    (hRadical : ∀ x, B F x = 0) :
    B g g = B r r := by
  have hgg : B g g + B r g = 0 := by
    have h := hRadical g
    rw [hF, haddLeft] at h
    exact h
  have hrr : B g r + B r r = 0 := by
    have h := hRadical r
    rw [hF, haddLeft] at h
    exact h
  rw [hsymm r g] at hgg
  linarith

/-- Equivalent identity in the more common decomposition convention
`F = g - r`. -/
theorem radicalDifferenceEnergyIdentity
    (B : V → V → ℝ) (F g r : V)
    (hF : F = g - r)
    (haddLeft : ∀ x y z, B (x + y) z = B x z + B y z)
    (hnegLeft : ∀ x y, B (-x) y = -B x y)
    (hsymm : ∀ x y, B x y = B y x)
    (hRadical : ∀ x, B F x = 0) :
    B g g = B r r := by
  have hF' : F = g + (-r) := by
    simpa [sub_eq_add_neg] using hF
  have h := radicalSplitEnergyIdentity B F g (-r) hF' haddLeft hsymm hRadical
  have hdiag : B (-r) (-r) = B r r := by
    rw [hnegLeft, hsymm r (-r), hnegLeft, neg_neg]
  simpa [hdiag] using h

end RadicalSplit

section ConditionedTransfer

/-- A multiplicative comparison on two selected directions transfers a strict
reference-energy ordering.

`m` and `M` are the lower and upper comparison constants, and `rho` bounds the
reference parity ratio `ePlus / eMinus`.  The bridge need not be close to an
isometry: it suffices that `M * rho < m`. -/
theorem conditionedParityTransfer
    (ePlus eMinus qPlus qMinus m M rho : ℝ)
    (_hePlus : 0 ≤ ePlus)
    (heMinus : 0 < eMinus)
    (hM : 0 ≤ M)
    (hUpper : qPlus ≤ M * ePlus)
    (hLower : m * eMinus ≤ qMinus)
    (hRatio : ePlus ≤ rho * eMinus)
    (hCondition : M * rho < m) :
    qPlus < qMinus := by
  have hRatioScaled : M * ePlus ≤ M * (rho * eMinus) :=
    mul_le_mul_of_nonneg_left hRatio hM
  have hConditionScaled := mul_lt_mul_of_pos_right hCondition heMinus
  nlinarith

/-- The same transfer certificate written with the condition number
`kappa = M / m`.  Division is avoided in the hypotheses so the theorem remains
usable over interval-certified rational bounds. -/
theorem conditionNumberParityTransfer
    (ePlus eMinus qPlus qMinus m M rho kappa : ℝ)
    (hePlus : 0 ≤ ePlus)
    (heMinus : 0 < eMinus)
    (hm : 0 < m)
    (hM : 0 ≤ M)
    (hUpper : qPlus ≤ M * ePlus)
    (hLower : m * eMinus ≤ qMinus)
    (hRatio : ePlus ≤ rho * eMinus)
    (hKappa : M ≤ kappa * m)
    (hMargin : kappa * rho < 1) :
    qPlus < qMinus := by
  have hm_nonneg : 0 ≤ m := le_of_lt hm
  have hkappa_nonneg : 0 ≤ kappa := by
    by_contra hk
    have hkneg : kappa < 0 := lt_of_not_ge hk
    have hkappam_neg : kappa * m < 0 := mul_neg_of_neg_of_pos hkneg hm
    nlinarith
  have hMrho : M * rho < m := by
    have hrho_nonneg : 0 ≤ rho := by
      by_contra hr
      have hrneg : rho < 0 := lt_of_not_ge hr
      have hprod : rho * eMinus < 0 := mul_neg_of_neg_of_pos hrneg heMinus
      nlinarith
    have h1 : M * rho ≤ (kappa * m) * rho :=
      mul_le_mul_of_nonneg_right hKappa hrho_nonneg
    have h2 := mul_lt_mul_of_pos_right hMargin hm
    nlinarith [mul_assoc kappa m rho]
  exact conditionedParityTransfer ePlus eMinus qPlus qMinus m M rho
    hePlus heMinus hM hUpper hLower hRatio hMrho

/-- Quartic-margin form of the certificate.  It is tailored to a reference
separation of the form `ePlus / eMinus ≤ C / λ⁴`, but uses only multiplication,
which is friendlier to exact and interval arithmetic.

The hypothesis `M * C < m * λ⁴` says precisely that the transfer distortion
`M/m` grows more slowly than the available quartic margin at this finite scale. -/
theorem quarticMarginParityTransfer
    (ePlus eMinus qPlus qMinus m M C lambda : ℝ)
    (_hePlus : 0 ≤ ePlus)
    (heMinus : 0 < eMinus)
    (hM : 0 ≤ M)
    (hLambda : 0 < lambda)
    (hUpper : qPlus ≤ M * ePlus)
    (hLower : m * eMinus ≤ qMinus)
    (hQuarticRatio : lambda ^ 4 * ePlus ≤ C * eMinus)
    (hQuarticMargin : M * C < m * lambda ^ 4) :
    qPlus < qMinus := by
  have hlambda4 : 0 < lambda ^ 4 := pow_pos hLambda 4
  have hUpperScaled :
      lambda ^ 4 * qPlus ≤ lambda ^ 4 * (M * ePlus) :=
    mul_le_mul_of_nonneg_left hUpper (le_of_lt hlambda4)
  have hQuarticScaled :
      M * (lambda ^ 4 * ePlus) ≤ M * (C * eMinus) :=
    mul_le_mul_of_nonneg_left hQuarticRatio hM
  have hMarginScaled :
      (M * C) * eMinus < (m * lambda ^ 4) * eMinus :=
    mul_lt_mul_of_pos_right hQuarticMargin heMinus
  have hLowerScaled :
      lambda ^ 4 * (m * eMinus) ≤ lambda ^ 4 * qMinus :=
    mul_le_mul_of_nonneg_left hLower (le_of_lt hlambda4)
  have hScaled : lambda ^ 4 * qPlus < lambda ^ 4 * qMinus := by
    nlinarith
  by_contra hnot
  have hReverse : qMinus ≤ qPlus := le_of_not_gt hnot
  have hReverseScaled : lambda ^ 4 * qMinus ≤ lambda ^ 4 * qPlus :=
    mul_le_mul_of_nonneg_left hReverse (le_of_lt hlambda4)
  exact (not_lt_of_ge hReverseScaled) hScaled

/-- Additive comparison errors may be absorbed into the multiplicative
condition-number budget when they are measured in units of the odd reference
energy. -/
theorem conditionedTransferWithAdditiveErrors
    (ePlus eMinus qPlus qMinus m M rho errPlus errMinus : ℝ)
    (_hePlus : 0 ≤ ePlus)
    (heMinus : 0 < eMinus)
    (hM : 0 ≤ M)
    (hUpper : qPlus ≤ M * ePlus + errPlus * eMinus)
    (hLower : (m - errMinus) * eMinus ≤ qMinus)
    (hRatio : ePlus ≤ rho * eMinus)
    (hCondition : M * rho + errPlus < m - errMinus) :
    qPlus < qMinus := by
  have hRatioScaled : M * ePlus ≤ M * (rho * eMinus) :=
    mul_le_mul_of_nonneg_left hRatio hM
  have hConditionScaled := mul_lt_mul_of_pos_right hCondition heMinus
  nlinarith

end ConditionedTransfer

end RiemannCvs.RadicalTailTransfer
