import RiemannCvs.FourierInversionBridge
import RiemannCvs.ParityProjection

/-!
# From compressed Fourier leakage to exact inversion-parity trial vectors

Finite prolate modes are not exact eigenvectors of the full Fourier transform.
After the Poisson/`𝓔` intertwining, their images therefore have only approximate
multiplicative inversion parity.  This file combines two previously isolated
facts:

1. the inversion-parity defect is the sum of an amplitude defect and the image
   of the exterior Fourier leakage;
2. exact parity projection costs quadratically in the norm of that defect.

The resulting estimates show that there is no square-root loss: a parity defect
of norm `O(sqrt d)` changes the projected quadratic energy by `O(d)`, provided
the form has a lower bound on the discarded parity component.

The analytic estimates on the concrete map `𝓔`, prolate leakage, and Weil form
remain explicit hypotheses.
-/

namespace RiemannCvs.CompressedParityProjection

section DefectSquare

variable {V W : Type*}
variable [AddCommGroup V] [Module ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Squaring the compressed-grading triangle bound costs at most a factor two. -/
theorem compressedDefectSqBound
    (fourier : V →ₗ[ℝ] V)
    (inversion : W →ₗ[ℝ] W)
    (E : V →ₗ[ℝ] W)
    (epsilon chi : ℝ) (f residual : V)
    (hintertwine : ∀ x, inversion (E x) = E (fourier x))
    (hdefect : fourier f = (epsilon * chi) • f + residual) :
    ‖inversion (E f) - epsilon • E f‖ ^ 2 ≤
      2 * ((|epsilon * (chi - 1)| * ‖E f‖) ^ 2 +
        ‖E residual‖ ^ 2) := by
  have h := RiemannCvs.FourierInversionBridge.compressedGradingDefectNormBound
    fourier inversion E epsilon chi f residual hintertwine hdefect
  have hleft : 0 ≤ ‖inversion (E f) - epsilon • E f‖ := norm_nonneg _
  have hright :
      0 ≤ |epsilon * (chi - 1)| * ‖E f‖ + ‖E residual‖ := by positivity
  have hsquare :
      ‖inversion (E f) - epsilon • E f‖ ^ 2 ≤
        (|epsilon * (chi - 1)| * ‖E f‖ + ‖E residual‖) ^ 2 := by
    nlinarith
  have hsum :
      (|epsilon * (chi - 1)| * ‖E f‖ + ‖E residual‖) ^ 2 ≤
        2 * ((|epsilon * (chi - 1)| * ‖E f‖) ^ 2 +
          ‖E residual‖ ^ 2) := by
    nlinarith [sq_nonneg (|epsilon * (chi - 1)| * ‖E f‖ - ‖E residual‖)]
  exact hsquare.trans hsum

/-- A dimensionless amplitude and residual budget converts the previous bound
into an `O(d)` estimate. -/
theorem compressedDefectSqBudget
    (defectSq amplitudeTermSq residualTermSq
      amplitudeBudget residualBudget d : ℝ)
    (hdefect : defectSq ≤ 2 * (amplitudeTermSq + residualTermSq))
    (hamplitude : amplitudeTermSq ≤ amplitudeBudget * d)
    (hresidual : residualTermSq ≤ residualBudget * d) :
    defectSq ≤ 2 * (amplitudeBudget + residualBudget) * d := by
  nlinarith

end DefectSquare

section ProjectedEnergy

variable {V W : Type*}
variable [AddCommGroup V] [Module ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Exact even-sector energy bound for a compressed Fourier `+1` mode.

The two scalar hypotheses `hAmplitudeBudget` and `hResidualBudget` are the only
analytic inputs needed to retain the defect scale after exact inversion-parity
projection. -/
theorem compressedPlusProjectionEnergyUpper
    (fourier : V →ₗ[ℝ] V)
    (J : W →ₗ[ℝ] W)
    (E : V →ₗ[ℝ] W)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (chi amplitudeBudget residualBudget d C : ℝ)
    (f residual : V)
    (hintertwine : ∀ x, J (E x) = E (fourier x))
    (hdefect : fourier f = chi • f + residual)
    (hAmplitudeBudget :
      (|chi - 1| * ‖E f‖) ^ 2 ≤ amplitudeBudget * d)
    (hResidualBudget : ‖E residual‖ ^ 2 ≤ residualBudget * d)
    (hJ : J (J (E f)) = E f)
    (hInvariant : ∀ x y, B (J x) (J y) = B x y)
    (hC : 0 ≤ C)
    (hOddLower :
      -(C * ‖RiemannCvs.ParityProjection.oddPart J (E f)‖ ^ 2) ≤
        B (RiemannCvs.ParityProjection.oddPart J (E f))
          (RiemannCvs.ParityProjection.oddPart J (E f))) :
    B (RiemannCvs.ParityProjection.evenPart J (E f))
        (RiemannCvs.ParityProjection.evenPart J (E f)) ≤
      B (E f) (E f) +
        (C / 2) * (amplitudeBudget + residualBudget) * d := by
  have hDefectSqRaw := compressedDefectSqBound
    fourier J E 1 chi f residual hintertwine (by simpa using hdefect)
  have hDefectSq :
      ‖E f - J (E f)‖ ^ 2 ≤
        2 * ((|chi - 1| * ‖E f‖) ^ 2 + ‖E residual‖ ^ 2) := by
    simpa [norm_sub_rev] using hDefectSqRaw
  have hBudget :
      ‖E f - J (E f)‖ ^ 2 ≤
        2 * (amplitudeBudget + residualBudget) * d :=
    compressedDefectSqBudget
      (‖E f - J (E f)‖ ^ 2)
      ((|chi - 1| * ‖E f‖) ^ 2)
      (‖E residual‖ ^ 2)
      amplitudeBudget residualBudget d
      hDefectSq hAmplitudeBudget hResidualBudget
  have hProjection :=
    RiemannCvs.ParityProjection.evenProjectionEnergyUpper
      J B (E f) C hJ hInvariant hOddLower
  have hscale :
      (C / 4) * ‖E f - J (E f)‖ ^ 2 ≤
        (C / 4) * (2 * (amplitudeBudget + residualBudget) * d) :=
    mul_le_mul_of_nonneg_left hBudget (by positivity)
  calc
    B (RiemannCvs.ParityProjection.evenPart J (E f))
        (RiemannCvs.ParityProjection.evenPart J (E f))
        ≤ B (E f) (E f) + (C / 4) * ‖E f - J (E f)‖ ^ 2 := hProjection
    _ ≤ B (E f) (E f) +
        (C / 4) * (2 * (amplitudeBudget + residualBudget) * d) :=
      add_le_add_left hscale _
    _ = B (E f) (E f) +
        (C / 2) * (amplitudeBudget + residualBudget) * d := by ring

/-- Exact odd-sector analogue of `compressedPlusProjectionEnergyUpper`. -/
theorem compressedMinusProjectionEnergyUpper
    (fourier : V →ₗ[ℝ] V)
    (J : W →ₗ[ℝ] W)
    (E : V →ₗ[ℝ] W)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (chi amplitudeBudget residualBudget d C : ℝ)
    (f residual : V)
    (hintertwine : ∀ x, J (E x) = E (fourier x))
    (hdefect : fourier f = (-chi) • f + residual)
    (hAmplitudeBudget :
      (|chi - 1| * ‖E f‖) ^ 2 ≤ amplitudeBudget * d)
    (hResidualBudget : ‖E residual‖ ^ 2 ≤ residualBudget * d)
    (hJ : J (J (E f)) = E f)
    (hInvariant : ∀ x y, B (J x) (J y) = B x y)
    (hC : 0 ≤ C)
    (hEvenLower :
      -(C * ‖RiemannCvs.ParityProjection.evenPart J (E f)‖ ^ 2) ≤
        B (RiemannCvs.ParityProjection.evenPart J (E f))
          (RiemannCvs.ParityProjection.evenPart J (E f))) :
    B (RiemannCvs.ParityProjection.oddPart J (E f))
        (RiemannCvs.ParityProjection.oddPart J (E f)) ≤
      B (E f) (E f) +
        (C / 2) * (amplitudeBudget + residualBudget) * d := by
  have hDefectSqRaw := compressedDefectSqBound
    fourier J E (-1) chi f residual hintertwine (by simpa using hdefect)
  have hDefectSq :
      ‖E f + J (E f)‖ ^ 2 ≤
        2 * ((|chi - 1| * ‖E f‖) ^ 2 + ‖E residual‖ ^ 2) := by
    simpa [add_comm, add_left_comm, add_assoc] using hDefectSqRaw
  have hBudget :
      ‖E f + J (E f)‖ ^ 2 ≤
        2 * (amplitudeBudget + residualBudget) * d :=
    compressedDefectSqBudget
      (‖E f + J (E f)‖ ^ 2)
      ((|chi - 1| * ‖E f‖) ^ 2)
      (‖E residual‖ ^ 2)
      amplitudeBudget residualBudget d
      hDefectSq hAmplitudeBudget hResidualBudget
  have hProjection :=
    RiemannCvs.ParityProjection.oddProjectionEnergyUpper
      J B (E f) C hJ hInvariant hEvenLower
  have hscale :
      (C / 4) * ‖E f + J (E f)‖ ^ 2 ≤
        (C / 4) * (2 * (amplitudeBudget + residualBudget) * d) :=
    mul_le_mul_of_nonneg_left hBudget (by positivity)
  calc
    B (RiemannCvs.ParityProjection.oddPart J (E f))
        (RiemannCvs.ParityProjection.oddPart J (E f))
        ≤ B (E f) (E f) + (C / 4) * ‖E f + J (E f)‖ ^ 2 := hProjection
    _ ≤ B (E f) (E f) +
        (C / 4) * (2 * (amplitudeBudget + residualBudget) * d) :=
      add_le_add_left hscale _
    _ = B (E f) (E f) +
        (C / 2) * (amplitudeBudget + residualBudget) * d := by ring

end ProjectedEnergy

end RiemannCvs.CompressedParityProjection
