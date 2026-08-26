import Mathlib

/-!
# A scale certificate for the high-mode correction in a constrained prolate root

The two-pole Weyl approximation has an error bounded by

`g * tailMass / (4 * lowResidueMass * highGap)`.

For fixed-index prolate modes, Parseval gives `tailMass = O(λ)`, while the next
same-Fourier-class defect is `Θ(λ⁸)` above the preceding one.  Hence the
normalized root correction is `O(λ⁻⁷)`.

This file formalizes only the multiplication-only rate extraction.  The
special-function and Parseval estimates remain explicit analytic inputs.
-/

namespace RiemannCvs.ProlateTailRate

/-- If a correction obeys the standard Weyl-tail numerator bound and the same
numerator has a `λ⁻⁷` budget relative to the denominator, then the correction
is itself `O(λ⁻⁷)`. -/
theorem lambdaSevenCorrectionCertificate
    (corr C lambda residueMass highGap g tailMass : ℝ)
    (hlambda : 0 < lambda)
    (hresidue : 0 < residueMass)
    (hgap : 0 < highGap)
    (hWeylTail :
      4 * residueMass * highGap * corr ≤ g * tailMass)
    (hScaledBudget :
      lambda ^ 7 * (g * tailMass) ≤
        4 * residueMass * highGap * C) :
    lambda ^ 7 * corr ≤ C := by
  have hlambda7 : 0 < lambda ^ 7 := pow_pos hlambda 7
  have hden : 0 < 4 * residueMass * highGap := by positivity
  have hscaled :=
    mul_le_mul_of_nonneg_left hWeylTail (le_of_lt hlambda7)
  have hcombined :
      (4 * residueMass * highGap) * (lambda ^ 7 * corr) ≤
        (4 * residueMass * highGap) * C := by
    calc
      (4 * residueMass * highGap) * (lambda ^ 7 * corr)
          = lambda ^ 7 * (4 * residueMass * highGap * corr) := by ring
      _ ≤ lambda ^ 7 * (g * tailMass) := hscaled
      _ ≤ 4 * residueMass * highGap * C := hScaledBudget
      _ = (4 * residueMass * highGap) * C := by ring
  exact (mul_le_mul_left hden).mp hcombined

/-- A direct finite-scale version: once the numerator is at most an `eps`
fraction of the positive denominator, the root correction is at most `eps`. -/
theorem finiteTailCorrectionCertificate
    (corr eps residueMass highGap g tailMass : ℝ)
    (hresidue : 0 < residueMass)
    (hgap : 0 < highGap)
    (hWeylTail :
      4 * residueMass * highGap * corr ≤ g * tailMass)
    (hBudget :
      g * tailMass ≤ 4 * residueMass * highGap * eps) :
    corr ≤ eps := by
  have hden : 0 < 4 * residueMass * highGap := by positivity
  have hcombined :
      (4 * residueMass * highGap) * corr ≤
        (4 * residueMass * highGap) * eps := by
    calc
      (4 * residueMass * highGap) * corr
          = 4 * residueMass * highGap * corr := by ring
      _ ≤ g * tailMass := hWeylTail
      _ ≤ 4 * residueMass * highGap * eps := hBudget
      _ = (4 * residueMass * highGap) * eps := by ring
  exact (mul_le_mul_left hden).mp hcombined

end RiemannCvs.ProlateTailRate
