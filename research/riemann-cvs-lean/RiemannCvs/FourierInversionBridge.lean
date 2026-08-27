import Mathlib

/-!
# Fourier grading and multiplicative inversion parity

The prolate construction begins in the reflection-even Schwartz space on the
additive real line. Inside that space there is a second grading, given by the
additive Fourier transform. The map `E` used in the zeta construction
intertwines this Fourier grading with inversion on the multiplicative variable.

This file formalizes only the linear-algebraic consequences of an assumed
intertwining identity. Poisson summation and concrete function-space hypotheses
remain external analytic inputs.
-/

namespace RiemannCvs.FourierInversionBridge

section Exact

variable {V W : Type*}
variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup W] [Module ℝ W]

theorem gradingEigenvectorTransfer
    (fourier : V →ₗ[ℝ] V)
    (inversion : W →ₗ[ℝ] W)
    (E : V →ₗ[ℝ] W)
    (epsilon : ℝ) (f : V)
    (hintertwine : ∀ x, inversion (E x) = E (fourier x))
    (heigen : fourier f = epsilon • f) :
    inversion (E f) = epsilon • E f := by
  rw [hintertwine f, heigen, map_smul]

theorem fourierPlusMapsToInversionEven
    (fourier : V →ₗ[ℝ] V)
    (inversion : W →ₗ[ℝ] W)
    (E : V →ₗ[ℝ] W)
    (f : V)
    (hintertwine : ∀ x, inversion (E x) = E (fourier x))
    (heigen : fourier f = f) :
    inversion (E f) = E f := by
  have h := gradingEigenvectorTransfer fourier inversion E 1 f
    hintertwine (by simpa using heigen)
  simpa using h

theorem fourierMinusMapsToInversionOdd
    (fourier : V →ₗ[ℝ] V)
    (inversion : W →ₗ[ℝ] W)
    (E : V →ₗ[ℝ] W)
    (f : V)
    (hintertwine : ∀ x, inversion (E x) = E (fourier x))
    (heigen : fourier f = -f) :
    inversion (E f) = -E f := by
  have h := gradingEigenvectorTransfer fourier inversion E (-1) f
    hintertwine (by simpa using heigen)
  simpa using h

end Exact

section Defect

variable {V W : Type*}
variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup W] [Module ℝ W]

theorem gradingDefectTransfer
    (fourier : V →ₗ[ℝ] V)
    (inversion : W →ₗ[ℝ] W)
    (E : V →ₗ[ℝ] W)
    (epsilon : ℝ) (f residual : V)
    (hintertwine : ∀ x, inversion (E x) = E (fourier x))
    (hdefect : fourier f = epsilon • f + residual) :
    inversion (E f) - epsilon • E f = E residual := by
  rw [hintertwine f, hdefect, map_add, map_smul]
  abel

theorem compressedGradingDefectTransfer
    (fourier : V →ₗ[ℝ] V)
    (inversion : W →ₗ[ℝ] W)
    (E : V →ₗ[ℝ] W)
    (epsilon chi : ℝ) (f residual : V)
    (hintertwine : ∀ x, inversion (E x) = E (fourier x))
    (hdefect : fourier f = (epsilon * chi) • f + residual) :
    inversion (E f) - epsilon • E f =
      (epsilon * (chi - 1)) • E f + E residual := by
  rw [hintertwine f, hdefect, map_add, map_smul]
  module

end Defect

section NormDefect

variable {V W : Type*}
variable [AddCommGroup V] [Module ℝ V]
variable [SeminormedAddCommGroup W] [NormedSpace ℝ W]

theorem gradingDefectNormBound
    (fourier : V →ₗ[ℝ] V)
    (inversion : W →ₗ[ℝ] W)
    (E : V →ₗ[ℝ] W)
    (epsilon : ℝ) (f residual : V)
    (bound : ℝ)
    (hintertwine : ∀ x, inversion (E x) = E (fourier x))
    (hdefect : fourier f = epsilon • f + residual)
    (hbound : ‖E residual‖ ≤ bound) :
    ‖inversion (E f) - epsilon • E f‖ ≤ bound := by
  rw [gradingDefectTransfer fourier inversion E epsilon f residual
    hintertwine hdefect]
  exact hbound

theorem compressedGradingDefectNormBound
    (fourier : V →ₗ[ℝ] V)
    (inversion : W →ₗ[ℝ] W)
    (E : V →ₗ[ℝ] W)
    (epsilon chi : ℝ) (f residual : V)
    (hintertwine : ∀ x, inversion (E x) = E (fourier x))
    (hdefect : fourier f = (epsilon * chi) • f + residual) :
    ‖inversion (E f) - epsilon • E f‖ ≤
      |epsilon * (chi - 1)| * ‖E f‖ + ‖E residual‖ := by
  rw [compressedGradingDefectTransfer fourier inversion E epsilon chi
    f residual hintertwine hdefect]
  calc
    ‖(epsilon * (chi - 1)) • E f + E residual‖
        ≤ ‖(epsilon * (chi - 1)) • E f‖ + ‖E residual‖ := norm_add_le _ _
    _ = |epsilon * (chi - 1)| * ‖E f‖ + ‖E residual‖ := by
      rw [norm_smul, Real.norm_eq_abs]

theorem compressedPlusDefectNormBound
    (fourier : V →ₗ[ℝ] V)
    (inversion : W →ₗ[ℝ] W)
    (E : V →ₗ[ℝ] W)
    (chi : ℝ) (f residual : V)
    (hintertwine : ∀ x, inversion (E x) = E (fourier x))
    (hdefect : fourier f = chi • f + residual) :
    ‖inversion (E f) - E f‖ ≤
      |chi - 1| * ‖E f‖ + ‖E residual‖ := by
  have h := compressedGradingDefectNormBound fourier inversion E 1 chi
    f residual hintertwine (by simpa using hdefect)
  simpa using h

theorem compressedMinusDefectNormBound
    (fourier : V →ₗ[ℝ] V)
    (inversion : W →ₗ[ℝ] W)
    (E : V →ₗ[ℝ] W)
    (chi : ℝ) (f residual : V)
    (hintertwine : ∀ x, inversion (E x) = E (fourier x))
    (hdefect : fourier f = (-chi) • f + residual) :
    ‖inversion (E f) + E f‖ ≤
      |chi - 1| * ‖E f‖ + ‖E residual‖ := by
  have h := compressedGradingDefectNormBound fourier inversion E (-1) chi
    f residual hintertwine (by simpa using hdefect)
  simpa [sub_eq_add_neg, abs_sub_comm] using h

end NormDefect

section PointwiseInversion

theorem pointwiseFourierClassGivesInversionParity
    (Ef Ehat : ℝ → ℝ) (epsilon u : ℝ)
    (hPoisson : Ehat u = Ef u⁻¹)
    (hclass : Ehat u = epsilon * Ef u) :
    Ef u⁻¹ = epsilon * Ef u := by
  linarith

end PointwiseInversion

end RiemannCvs.FourierInversionBridge
