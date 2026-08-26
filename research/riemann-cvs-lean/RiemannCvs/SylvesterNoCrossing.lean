import Mathlib

/-!
# Rank-one Sylvester relations and parity crossings

A recurring finite CvS identity has the form

`J Q₊ - Q₋ J = β ⊗ η`.

The theorem below records a useful obstruction to a common eigenvalue.  It is
stated with a left eigenfunctional for `Q₋`, so no inner-product or
self-adjointness boilerplate is needed.  In a self-adjoint application the left
eigenfunctional is obtained by pairing with an odd eigenvector.
-/

namespace RiemannCvs.SylvesterNoCrossing

variable {E O : Type*}
variable [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup O] [Module ℝ O]

/-- A common eigenvalue of the two sides of a rank-one Sylvester relation
forces one of the two boundary overlaps to vanish. -/
theorem commonEigenvalueForcesBoundaryZero
    (Qplus : E →ₗ[ℝ] E)
    (Qminus : O →ₗ[ℝ] O)
    (J : E →ₗ[ℝ] O)
    (eta : E →ₗ[ℝ] ℝ)
    (phi : O →ₗ[ℝ] ℝ)
    (beta : O)
    (x : E)
    (lambda : ℝ)
    (hSylvester :
      ∀ z, J (Qplus z) - Qminus (J z) = eta z • beta)
    (hx : Qplus x = lambda • x)
    (hphi : ∀ z, phi (Qminus z) = lambda * phi z) :
    eta x * phi beta = 0 := by
  have h := congrArg (fun z => phi z) (hSylvester x)
  rw [map_sub, map_smul, hx, J.map_smul, hphi] at h
  simp only [LinearMap.map_smul_of_tower, smul_eq_mul] at h
  nlinarith

/-- If both boundary overlaps are nonzero, the same scalar cannot occur on both
sides of the Sylvester relation. -/
theorem noCommonEigenvalueWhenBoundaryOverlapsNonzero
    (Qplus : E →ₗ[ℝ] E)
    (Qminus : O →ₗ[ℝ] O)
    (J : E →ₗ[ℝ] O)
    (eta : E →ₗ[ℝ] ℝ)
    (phi : O →ₗ[ℝ] ℝ)
    (beta : O)
    (x : E)
    (lambda : ℝ)
    (hSylvester :
      ∀ z, J (Qplus z) - Qminus (J z) = eta z • beta)
    (hx : Qplus x = lambda • x)
    (hphi : ∀ z, phi (Qminus z) = lambda * phi z)
    (heta : eta x ≠ 0)
    (hbeta : phi beta ≠ 0) :
    False := by
  have hzero := commonEigenvalueForcesBoundaryZero
    Qplus Qminus J eta phi beta x lambda hSylvester hx hphi
  exact mul_ne_zero heta hbeta hzero

end RiemannCvs.SylvesterNoCrossing
