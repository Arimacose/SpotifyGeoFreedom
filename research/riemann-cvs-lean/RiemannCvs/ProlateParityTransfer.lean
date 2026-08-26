import Mathlib

/-!
# Prolate parity separation and robust transfer

This file isolates the finite-dimensional inequality needed to turn a
four-power separation in a prolate reference model into a strict ordering of
even and odd constrained energies, while keeping explicit control of:

* leakage from the lowest mode in each parity sector;
* the high-mode correction to the two-pole Weyl approximation;
* one-sided comparison errors when passing from the prolate model to a Weil
  quadratic form.

No prolate asymptotic, trace formula, or Riemann-hypothesis statement is assumed
implicitly.  Those analytic inputs appear only as hypotheses of the theorems.
-/

namespace RiemannCvs.ProlateParityTransfer

/-- The two-pole weight obtained from the squared boundary-value ratio
`r₄ / r₀ = 3 / 8` in the Fourier-even Hermite model. -/
theorem evenTwoPoleWeight :
    (1 : ℝ) / (1 + 3 / 8) = 8 / 11 := by
  norm_num

/-- The two-pole weight obtained from the squared boundary-value ratio
`r₆ / r₂ = 5 / 8` in the Fourier-odd Hermite model. -/
theorem oddTwoPoleWeight :
    (1 : ℝ) / (1 + 5 / 8) = 8 / 13 := by
  norm_num

/-- Normalizing the two boundary-zero candidates multiplies the fixed-index
Fuchs ratio by `13 / 11`.  Thus the coefficient

`(13/11) * (15/(128 π²))`

simplifies to `195/(1408 π²)`.  The analytic assertion that a ratio is
asymptotic to this coefficient times `λ⁻⁴` is deliberately not part of this
algebraic theorem. -/
theorem normalizedFuchsQuarticConstant :
    (13 / 11 : ℝ) * (15 / (128 * Real.pi ^ 2)) =
      195 / (1408 * Real.pi ^ 2) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]
  ring

/-- Dimensionless upper and lower bounds for two boundary-constrained spectral
locations.

Interpretation of the variables:

* `d₀ < d₄` and `d₂ < d₆` are the first two defect eigenvalues in the two
  parity sectors;
* `etaPlus`, `etaMinus` are the normalized locations of the constrained roots
  inside those gaps;
* the exact two-pole locations are `8/11` and `8/13`;
* `delta` is an upper bound for the downward high-mode correction in the odd
  sector;
* `alpha₀`, `alpha₂` control the lower-mode defects relative to `d₄`, `d₆`.

The theorem does not assert that these hypotheses hold for a particular
operator. -/
theorem constrainedParityBounds
    (d₀ d₂ d₄ d₆ etaPlus etaMinus nuPlus nuMinus
      alpha₀ alpha₂ delta : ℝ)
    (hd₀_nonneg : 0 ≤ d₀)
    (hd₂_nonneg : 0 ≤ d₂)
    (horderPlus : d₀ ≤ d₄)
    (horderMinus : d₂ ≤ d₆)
    (hd₀_rel : d₀ ≤ alpha₀ * d₄)
    (hd₂_rel : d₂ ≤ alpha₂ * d₆)
    (hetaPlus : etaPlus ≤ (8 / 11 : ℝ))
    (hetaMinus : (8 / 13 : ℝ) - delta ≤ etaMinus)
    (hoddWeight : 0 ≤ (8 / 13 : ℝ) - delta)
    (hnuPlus : nuPlus = d₀ + etaPlus * (d₄ - d₀))
    (hnuMinus : nuMinus = d₂ + etaMinus * (d₆ - d₂)) :
    nuPlus ≤ (alpha₀ + 8 / 11) * d₄ ∧
      ((8 / 13 : ℝ) - delta) * (1 - alpha₂) * d₆ ≤ nuMinus := by
  have hgapPlus : 0 ≤ d₄ - d₀ := sub_nonneg.mpr horderPlus
  have hetaGapPlus :
      etaPlus * (d₄ - d₀) ≤ (8 / 11 : ℝ) * (d₄ - d₀) :=
    mul_le_mul_of_nonneg_right hetaPlus hgapPlus
  have hupper : nuPlus ≤ (alpha₀ + 8 / 11) * d₄ := by
    rw [hnuPlus]
    nlinarith

  have hgapMinus : 0 ≤ d₆ - d₂ := sub_nonneg.mpr horderMinus
  have hetaGapMinus :
      ((8 / 13 : ℝ) - delta) * (d₆ - d₂) ≤
        etaMinus * (d₆ - d₂) :=
    mul_le_mul_of_nonneg_right hetaMinus hgapMinus
  have hrelativeGap :
      (1 - alpha₂) * d₆ ≤ d₆ - d₂ := by
    nlinarith
  have hweightedRelativeGap :
      ((8 / 13 : ℝ) - delta) * ((1 - alpha₂) * d₆) ≤
        ((8 / 13 : ℝ) - delta) * (d₆ - d₂) :=
    mul_le_mul_of_nonneg_left hrelativeGap hoddWeight
  have hlower :
      ((8 / 13 : ℝ) - delta) * (1 - alpha₂) * d₆ ≤ nuMinus := by
    rw [hnuMinus]
    nlinarith
  exact ⟨hupper, hlower⟩

/-- A strict parity ordering follows once the dimensionless prolate margin is
positive.

In the intended application, `ratio` is of order `λ⁻⁴`. -/
theorem constrainedParitySeparation
    (d₀ d₂ d₄ d₆ etaPlus etaMinus nuPlus nuMinus
      alpha₀ alpha₂ delta ratio : ℝ)
    (hd₀_nonneg : 0 ≤ d₀)
    (hd₂_nonneg : 0 ≤ d₂)
    (hd₆_pos : 0 < d₆)
    (halpha₀ : 0 ≤ alpha₀)
    (horderPlus : d₀ ≤ d₄)
    (horderMinus : d₂ ≤ d₆)
    (hd₀_rel : d₀ ≤ alpha₀ * d₄)
    (hd₂_rel : d₂ ≤ alpha₂ * d₆)
    (hratio : d₄ ≤ ratio * d₆)
    (hetaPlus : etaPlus ≤ (8 / 11 : ℝ))
    (hetaMinus : (8 / 13 : ℝ) - delta ≤ etaMinus)
    (hoddWeight : 0 ≤ (8 / 13 : ℝ) - delta)
    (hnuPlus : nuPlus = d₀ + etaPlus * (d₄ - d₀))
    (hnuMinus : nuMinus = d₂ + etaMinus * (d₆ - d₂))
    (hmargin :
      (alpha₀ + 8 / 11) * ratio <
        ((8 / 13 : ℝ) - delta) * (1 - alpha₂)) :
    nuPlus < nuMinus := by
  obtain ⟨hupper, hlower⟩ := constrainedParityBounds
    d₀ d₂ d₄ d₆ etaPlus etaMinus nuPlus nuMinus
    alpha₀ alpha₂ delta hd₀_nonneg hd₂_nonneg horderPlus horderMinus
    hd₀_rel hd₂_rel hetaPlus hetaMinus hoddWeight hnuPlus hnuMinus
  have hcoef : 0 ≤ alpha₀ + (8 / 11 : ℝ) := by
    nlinarith
  have hratioScaled :
      (alpha₀ + 8 / 11) * d₄ ≤
        (alpha₀ + 8 / 11) * (ratio * d₆) :=
    mul_le_mul_of_nonneg_left hratio hcoef
  have hmarginScaled := mul_lt_mul_of_pos_right hmargin hd₆_pos
  nlinarith

/-- Robust transfer to another quadratic form using one-sided comparison
errors measured in units of the odd reference scale `d₆`.

This is the exact finite-scale certificate needed from a trace-formula bridge:
an upper comparison in the even sector, a lower comparison in the odd sector,
and an error smaller than the prolate parity margin. -/
theorem oneSidedWeilParityTransfer
    (d₀ d₂ d₄ d₆ etaPlus etaMinus nuPlus nuMinus qPlus qMinus
      alpha₀ alpha₂ delta ratio errPlus errMinus : ℝ)
    (hd₀_nonneg : 0 ≤ d₀)
    (hd₂_nonneg : 0 ≤ d₂)
    (hd₆_pos : 0 < d₆)
    (halpha₀ : 0 ≤ alpha₀)
    (horderPlus : d₀ ≤ d₄)
    (horderMinus : d₂ ≤ d₆)
    (hd₀_rel : d₀ ≤ alpha₀ * d₄)
    (hd₂_rel : d₂ ≤ alpha₂ * d₆)
    (hratio : d₄ ≤ ratio * d₆)
    (hetaPlus : etaPlus ≤ (8 / 11 : ℝ))
    (hetaMinus : (8 / 13 : ℝ) - delta ≤ etaMinus)
    (hoddWeight : 0 ≤ (8 / 13 : ℝ) - delta)
    (hnuPlus : nuPlus = d₀ + etaPlus * (d₄ - d₀))
    (hnuMinus : nuMinus = d₂ + etaMinus * (d₆ - d₂))
    (hqPlus : qPlus ≤ nuPlus + errPlus * d₆)
    (hqMinus : nuMinus - errMinus * d₆ ≤ qMinus)
    (hmargin :
      (alpha₀ + 8 / 11) * ratio + errPlus <
        ((8 / 13 : ℝ) - delta) * (1 - alpha₂) - errMinus) :
    qPlus < qMinus := by
  obtain ⟨hupper, hlower⟩ := constrainedParityBounds
    d₀ d₂ d₄ d₆ etaPlus etaMinus nuPlus nuMinus
    alpha₀ alpha₂ delta hd₀_nonneg hd₂_nonneg horderPlus horderMinus
    hd₀_rel hd₂_rel hetaPlus hetaMinus hoddWeight hnuPlus hnuMinus
  have hcoef : 0 ≤ alpha₀ + (8 / 11 : ℝ) := by
    nlinarith
  have hratioScaled :
      (alpha₀ + 8 / 11) * d₄ ≤
        (alpha₀ + 8 / 11) * (ratio * d₆) :=
    mul_le_mul_of_nonneg_left hratio hcoef
  have hmarginScaled := mul_lt_mul_of_pos_right hmargin hd₆_pos
  nlinarith

/-- Symmetric absolute-error version of `oneSidedWeilParityTransfer`. -/
theorem absoluteErrorWeilParityTransfer
    (d₀ d₂ d₄ d₆ etaPlus etaMinus nuPlus nuMinus qPlus qMinus
      alpha₀ alpha₂ delta ratio err : ℝ)
    (hd₀_nonneg : 0 ≤ d₀)
    (hd₂_nonneg : 0 ≤ d₂)
    (hd₆_pos : 0 < d₆)
    (halpha₀ : 0 ≤ alpha₀)
    (herr : 0 ≤ err)
    (horderPlus : d₀ ≤ d₄)
    (horderMinus : d₂ ≤ d₆)
    (hd₀_rel : d₀ ≤ alpha₀ * d₄)
    (hd₂_rel : d₂ ≤ alpha₂ * d₆)
    (hratio : d₄ ≤ ratio * d₆)
    (hetaPlus : etaPlus ≤ (8 / 11 : ℝ))
    (hetaMinus : (8 / 13 : ℝ) - delta ≤ etaMinus)
    (hoddWeight : 0 ≤ (8 / 13 : ℝ) - delta)
    (hnuPlus : nuPlus = d₀ + etaPlus * (d₄ - d₀))
    (hnuMinus : nuMinus = d₂ + etaMinus * (d₆ - d₂))
    (hqPlus : |qPlus - nuPlus| ≤ err * d₆)
    (hqMinus : |qMinus - nuMinus| ≤ err * d₆)
    (hmargin :
      (alpha₀ + 8 / 11) * ratio + err <
        ((8 / 13 : ℝ) - delta) * (1 - alpha₂) - err) :
    qPlus < qMinus := by
  have herrScale : 0 ≤ err * d₆ := mul_nonneg herr (le_of_lt hd₆_pos)
  have hqPlusOneSided : qPlus ≤ nuPlus + err * d₆ := by
    have h := (abs_le.mp hqPlus).2
    linarith
  have hqMinusOneSided : nuMinus - err * d₆ ≤ qMinus := by
    have h := (abs_le.mp hqMinus).1
    linarith
  exact oneSidedWeilParityTransfer
    d₀ d₂ d₄ d₆ etaPlus etaMinus nuPlus nuMinus qPlus qMinus
    alpha₀ alpha₂ delta ratio err err
    hd₀_nonneg hd₂_nonneg hd₆_pos halpha₀ horderPlus horderMinus
    hd₀_rel hd₂_rel hratio hetaPlus hetaMinus hoddWeight
    hnuPlus hnuMinus hqPlusOneSided hqMinusOneSided hmargin

end RiemannCvs.ProlateParityTransfer
