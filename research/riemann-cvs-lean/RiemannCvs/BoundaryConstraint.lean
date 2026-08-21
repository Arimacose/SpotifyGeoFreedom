import Mathlib

/-!
# Boundary-constrained and displacement reductions for finite Weil matrices

This file records three finite-dimensional reductions:

1. a rank-two displacement identity turns a boundary coefficient of an even
   eigenvector into an odd-sector resolvent equation;
2. the lowest Rayleigh quotient under a boundary constraint gives a stable
   certificate for the ground eigenline even when the first spectral gap
   collapses;
3. a boundary-null vector made from the first two eigenmodes converts that
   certificate into a bound depending only on their boundary coefficients.

The analytic and spectral inputs are explicit hypotheses. The conclusions are
algebraic or order-theoretic and contain no asymptotic assumption.
-/

namespace RiemannCvs.BoundaryConstraint

section BoundaryLine

variable {𝕜 V : Type*}
variable [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- The canonical vector in `span{x₀,x₁}` killed by a linear functional. -/
theorem boundaryNullCombination
    (ell : V →ₗ[𝕜] 𝕜) (x₀ x₁ : V) :
    ell ((ell x₁) • x₀ - (ell x₀) • x₁) = 0 := by
  simp only [map_sub, map_smul, smul_eq_mul]
  ring

/-- In the affine chart `x₀ + r • x₁`, the boundary-null slope is unique. -/
theorem boundaryNullSlope
    (ell : V →ₗ[𝕜] 𝕜) (x₀ x₁ : V) (r : 𝕜)
    (h₁ : ell x₁ ≠ 0)
    (hnull : ell (x₀ + r • x₁) = 0) :
    r = -(ell x₀) / ell x₁ := by
  have hscalar : ell x₀ + r * ell x₁ = 0 := by
    simpa only [map_add, map_smul, smul_eq_mul] using hnull
  apply (eq_div_iff h₁).2
  linear_combination hscalar

/-- Scalar identity underlying the exact overlap defect of the normalized
boundary-null line in an orthonormal two-dimensional eigenspace. -/
theorem boundaryOverlapDefect
    (c₀ c₁ : 𝕜) (hden : c₀ * c₀ + c₁ * c₁ ≠ 0) :
    1 - (c₁ * c₁) / (c₀ * c₀ + c₁ * c₁) =
      (c₀ * c₀) / (c₀ * c₀ + c₁ * c₁) := by
  rw [one_sub_div hden]
  ring

end BoundaryLine

section Displacement

variable {𝕜 V : Type*}
variable [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- Eigenvector consequence of a rank-one displacement equation.

For a finite Loewner/Weil matrix one has schematically
`D Q - Q D = p ⊗ 1 - 1 ⊗ p`. On an even eigenvector `x`, the odd functional
vanishes, leaving `D(Qx) - Q(Dx) = c • p`, where `c` is the boundary
coefficient. -/
theorem displacementEigenvectorEquation
    (D Q : V →ₗ[𝕜] V) (x p : V) (lambda c : 𝕜)
    (hEig : Q x = lambda • x)
    (hDisp : D (Q x) - Q (D x) = c • p) :
    Q (D x) - lambda • D x = -(c • p) := by
  have hD : D (Q x) = lambda • D x := by
    rw [hEig, map_smul]
  rw [hD] at hDisp
  have hneg := congrArg (fun z : V => -z) hDisp
  simpa only [neg_sub] using hneg

/-- Applying an odd-sector reduced inverse to the displacement equation. -/
theorem displacementResolventEquation
    (R Q D : V →ₗ[𝕜] V) (x p : V) (lambda c : 𝕜)
    (hEq : Q (D x) - lambda • D x = -(c • p))
    (hInv : R (Q (D x) - lambda • D x) = D x) :
    D x = (-c) • R p := by
  calc
    D x = R (Q (D x) - lambda • D x) := hInv.symm
    _ = R (-(c • p)) := by rw [hEq]
    _ = (-c) • R p := by simp

end Displacement

section VariationalCertificate

/-- Scalar spectral-weight form of the constrained-ground overlap estimate.

In the intended application, `w = |⟪x₀,y⟫|²`, `nu` is the Rayleigh quotient of
a unit boundary-constrained vector `y`, `lambda₀ < lambda₁` are the first two
eigenvalues, and `tail` is the contribution of all excited spectral weights. -/
theorem spectralWeightDefectBound
    (lambda₀ lambda₁ nu w tail : ℝ)
    (hgap : lambda₀ < lambda₁)
    (hdecomp : nu = w * lambda₀ + tail)
    (htail : (1 - w) * lambda₁ ≤ tail) :
    1 - w ≤ (nu - lambda₀) / (lambda₁ - lambda₀) := by
  have hpos : 0 < lambda₁ - lambda₀ := sub_pos.mpr hgap
  apply (le_div_iff₀ hpos).2
  rw [hdecomp]
  nlinarith

/-- Equivalent lower bound on the ground-state spectral weight. -/
theorem spectralWeightLowerBound
    (lambda₀ lambda₁ nu w tail : ℝ)
    (hgap : lambda₀ < lambda₁)
    (hdecomp : nu = w * lambda₀ + tail)
    (htail : (1 - w) * lambda₁ ≤ tail) :
    1 - (nu - lambda₀) / (lambda₁ - lambda₀) ≤ w := by
  have h := spectralWeightDefectBound lambda₀ lambda₁ nu w tail
    hgap hdecomp htail
  linarith

/-- If the constrained Rayleigh excess is at most `eta` times the first gap,
then the ground-state weight is at least `1 - eta`. -/
theorem constrainedGroundCertificate
    (lambda₀ lambda₁ nu w tail eta : ℝ)
    (hgap : lambda₀ < lambda₁)
    (hdecomp : nu = w * lambda₀ + tail)
    (htail : (1 - w) * lambda₁ ≤ tail)
    (heta : nu - lambda₀ ≤ eta * (lambda₁ - lambda₀)) :
    1 - eta ≤ w := by
  have hpos : 0 < lambda₁ - lambda₀ := sub_pos.mpr hgap
  have hdef := spectralWeightDefectBound lambda₀ lambda₁ nu w tail
    hgap hdecomp htail
  have hquot : (nu - lambda₀) / (lambda₁ - lambda₀) ≤ eta := by
    exact (div_le_iff₀ hpos).2 heta
  linarith

/-- Exact normalized Rayleigh excess of the two-mode boundary-null test vector
`c₁ x₀ - c₀ x₁`, assuming `x₀,x₁` are orthonormal eigenvectors with
eigenvalues `lambda₀,lambda₁` and boundary coefficients `c₀,c₁`. -/
theorem twoModeRayleighExcess
    (lambda₀ lambda₁ c₀ c₁ : ℝ)
    (hden : c₀ ^ 2 + c₁ ^ 2 ≠ 0) :
    (c₁ ^ 2 * lambda₀ + c₀ ^ 2 * lambda₁) /
          (c₀ ^ 2 + c₁ ^ 2) - lambda₀ =
      (c₀ ^ 2 / (c₀ ^ 2 + c₁ ^ 2)) * (lambda₁ - lambda₀) := by
  field_simp [hden]
  ring

/-- If the constrained minimum `nu` is no larger than the Rayleigh quotient of
the two-mode boundary-null test vector, then its excess divided by the first
spectral gap is controlled solely by the boundary coefficient ratio. -/
theorem constrainedExcessFromTwoMode
    (lambda₀ lambda₁ nu c₀ c₁ : ℝ)
    (hgap : lambda₀ < lambda₁)
    (hden : c₀ ^ 2 + c₁ ^ 2 ≠ 0)
    (hnu :
      nu ≤ (c₁ ^ 2 * lambda₀ + c₀ ^ 2 * lambda₁) /
        (c₀ ^ 2 + c₁ ^ 2)) :
    (nu - lambda₀) / (lambda₁ - lambda₀) ≤
      c₀ ^ 2 / (c₀ ^ 2 + c₁ ^ 2) := by
  have hpos : 0 < lambda₁ - lambda₀ := sub_pos.mpr hgap
  apply (div_le_iff₀ hpos).2
  calc
    nu - lambda₀ ≤
        (c₁ ^ 2 * lambda₀ + c₀ ^ 2 * lambda₁) /
          (c₀ ^ 2 + c₁ ^ 2) - lambda₀ :=
      sub_le_sub_right hnu lambda₀
    _ = (c₀ ^ 2 / (c₀ ^ 2 + c₁ ^ 2)) *
        (lambda₁ - lambda₀) :=
      twoModeRayleighExcess lambda₀ lambda₁ c₀ c₁ hden

/-- Gap-normalized ground-state defect certificate obtained by combining the
spectral-weight inequality with the two-mode boundary-null trial vector. The
absolute size of the collapsing first gap no longer appears in the result. -/
theorem groundWeightDefectFromTwoMode
    (lambda₀ lambda₁ nu w tail c₀ c₁ : ℝ)
    (hgap : lambda₀ < lambda₁)
    (hdecomp : nu = w * lambda₀ + tail)
    (htail : (1 - w) * lambda₁ ≤ tail)
    (hden : c₀ ^ 2 + c₁ ^ 2 ≠ 0)
    (hnu :
      nu ≤ (c₁ ^ 2 * lambda₀ + c₀ ^ 2 * lambda₁) /
        (c₀ ^ 2 + c₁ ^ 2)) :
    1 - w ≤ c₀ ^ 2 / (c₀ ^ 2 + c₁ ^ 2) := by
  calc
    1 - w ≤ (nu - lambda₀) / (lambda₁ - lambda₀) :=
      spectralWeightDefectBound lambda₀ lambda₁ nu w tail
        hgap hdecomp htail
    _ ≤ c₀ ^ 2 / (c₀ ^ 2 + c₁ ^ 2) :=
      constrainedExcessFromTwoMode lambda₀ lambda₁ nu c₀ c₁
        hgap hden hnu

/-- Equivalent lower bound on the ground-state spectral weight produced by the
two-mode boundary certificate. -/
theorem groundWeightLowerBoundFromTwoMode
    (lambda₀ lambda₁ nu w tail c₀ c₁ : ℝ)
    (hgap : lambda₀ < lambda₁)
    (hdecomp : nu = w * lambda₀ + tail)
    (htail : (1 - w) * lambda₁ ≤ tail)
    (hden : c₀ ^ 2 + c₁ ^ 2 ≠ 0)
    (hnu :
      nu ≤ (c₁ ^ 2 * lambda₀ + c₀ ^ 2 * lambda₁) /
        (c₀ ^ 2 + c₁ ^ 2)) :
    1 - c₀ ^ 2 / (c₀ ^ 2 + c₁ ^ 2) ≤ w := by
  have h := groundWeightDefectFromTwoMode
    lambda₀ lambda₁ nu w tail c₀ c₁ hgap hdecomp htail hden hnu
  linarith

end VariationalCertificate

end RiemannCvs.BoundaryConstraint
