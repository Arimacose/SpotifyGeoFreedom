import Mathlib

/-!
# Fourier grading and multiplicative inversion parity

The prolate construction begins in the reflection-even Schwartz space on the
additive real line.  Inside that space there is a second grading, given by the
additive Fourier transform.  The map `𝓔` used in the zeta construction
intertwines this Fourier grading with inversion on the multiplicative variable;
analytically, the intertwining identity is a consequence of Poisson summation
when `f(0) = f̂(0) = 0`.

This file formalizes the linear-algebraic consequences of that analytic
intertwining.  It deliberately does not formalize Poisson summation or assert
that a concrete function belongs to the required Schwartz class.
-/

namespace RiemannCvs.FourierInversionBridge

section Exact

variable {V W : Type*}
variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup W] [Module ℝ W]

/-- An exact eigenvector of a source grading is sent to an exact eigenvector of
the intertwined target grading with the same eigenvalue. -/
theorem gradingEigenvectorTransfer
    (fourier : V →ₗ[ℝ] V)
    (inversion : W →ₗ[ℝ] W)
    (E : V →ₗ[ℝ] W)
    (epsilon : ℝ) (f : V)
    (hintertwine : ∀ x, inversion (E x) = E (fourier x))
    (heigen : fourier f = epsilon • f) :
    inversion (E f) = epsilon • E f := by
  rw [hintertwine f, heigen, map_smul]

/-- Fourier `+1` vectors map to inversion-even vectors. -/
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

/-- Fourier `-1` vectors map to inversion-odd vectors. -/
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

/-- Exact defect identity.  If the source vector obeys

`fourier f = epsilon • f + residual`,

then the failure of the image to have target parity `epsilon` is exactly the
image of the residual.  In the prolate application the residual is the Fourier
leakage outside the time window. -/
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

/-- Exact compressed-eigenvalue defect identity.  A time-limited prolate mode
has a full Fourier transform of the form

`fourier f = (epsilon * chi) • f + residual`,

where `chi` is the concentration amplitude and `residual` is supported outside
the time window.  The target inversion-parity defect splits into the amplitude
loss and the transformed leakage. -/
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

/-- If a norm estimate for the map `E` is available on the residual direction,
then the inversion-parity defect inherits the same estimate. -/
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

/-- Triangle-inequality bound for the finite-prolate inversion-parity defect. -/
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
      simp [Real.norm_eq_abs]

/-- Fourier `+1` specialization of the compressed defect bound. -/
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

/-- Fourier `-1` specialization of the compressed defect bound. -/
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
  simpa [sub_eq_add_neg] using h

end NormDefect

section PointwiseInversion

/-- Pointwise form of the Poisson-intertwining consequence.  If a transform
`Ehat` satisfies `Ehat u = Ef (u⁻¹)` and the source is in the Fourier
`epsilon`-class, represented by `Ehat = epsilon • Ef`, then `Ef` has
multiplicative inversion parity `epsilon`. -/
theorem pointwiseFourierClassGivesInversionParity
    (Ef Ehat : ℝ → ℝ) (epsilon u : ℝ)
    (hPoisson : Ehat u = Ef u⁻¹)
    (hclass : Ehat u = epsilon * Ef u) :
    Ef u⁻¹ = epsilon * Ef u := by
  linarith

end PointwiseInversion

end RiemannCvs.FourierInversionBridge
