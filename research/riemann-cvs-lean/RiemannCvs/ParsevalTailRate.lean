import Mathlib

/-!
# Explicit Parseval tail-mass rate

For the boundary functional `L(f) = integral f` on an interval of length
`2 * lambda`, Parseval gives total spectral residue mass `2 * lambda`.  Combining
that exact mass budget with an internal high-mode gap of order `lambda⁸` turns
the standard two-pole Weyl-tail correction into an order `lambda⁻⁷` term.

This file proves the multiplication-only rate extraction.  The Hilbert-space
Parseval identity and the prolate high-gap estimate remain explicit analytic
inputs when the theorem is instantiated.
-/

namespace RiemannCvs.ParsevalTailRate

/-- Explicit finite-scale certificate.

Hypotheses encode:

* `tailMass ≤ 2 * lambda` (Parseval/Bessel for the interval integral);
* `highGap ≥ gapConstant * lambda⁸ * localGap`;
* the standard Weyl-tail correction inequality.

The conclusion is the dimensionless estimate

`2 * residueMass * gapConstant * lambda⁷ * correction ≤ 1`.
-/
theorem parsevalLambdaSevenCertificate
    (correction residueMass gapConstant lambda localGap highGap tailMass : ℝ)
    (hCorrection : 0 ≤ correction)
    (hResidue : 0 < residueMass)
    (hGapConstant : 0 < gapConstant)
    (hLambda : 0 < lambda)
    (hLocalGap : 0 < localGap)
    (hTailMass : tailMass ≤ 2 * lambda)
    (hHighGap :
      gapConstant * lambda ^ 8 * localGap ≤ highGap)
    (hWeylTail :
      4 * residueMass * highGap * correction ≤
        localGap * tailMass) :
    2 * residueMass * gapConstant * lambda ^ 7 * correction ≤ 1 := by
  have hMultiplier : 0 ≤ 4 * residueMass * correction := by positivity
  have hHighScaled :
      4 * residueMass * correction *
          (gapConstant * lambda ^ 8 * localGap) ≤
        4 * residueMass * correction * highGap :=
    mul_le_mul_of_nonneg_left hHighGap hMultiplier
  have hTailScaled :
      localGap * tailMass ≤ localGap * (2 * lambda) :=
    mul_le_mul_of_nonneg_left hTailMass (le_of_lt hLocalGap)
  have hPositiveScale : 0 < 2 * localGap * lambda := by positivity
  have hCombined :
      (2 * localGap * lambda) *
          (2 * residueMass * gapConstant * lambda ^ 7 * correction) ≤
        (2 * localGap * lambda) * 1 := by
    calc
      (2 * localGap * lambda) *
          (2 * residueMass * gapConstant * lambda ^ 7 * correction) =
        4 * residueMass * correction *
          (gapConstant * lambda ^ 8 * localGap) := by ring
      _ ≤ 4 * residueMass * correction * highGap := hHighScaled
      _ = 4 * residueMass * highGap * correction := by ring
      _ ≤ localGap * tailMass := hWeylTail
      _ ≤ localGap * (2 * lambda) := hTailScaled
      _ = (2 * localGap * lambda) * 1 := by ring
  exact (mul_le_mul_left hPositiveScale).mp hCombined

/-- Usual divided form of the same estimate. -/
theorem parsevalLambdaSevenUpperBound
    (correction residueMass gapConstant lambda localGap highGap tailMass : ℝ)
    (hCorrection : 0 ≤ correction)
    (hResidue : 0 < residueMass)
    (hGapConstant : 0 < gapConstant)
    (hLambda : 0 < lambda)
    (hLocalGap : 0 < localGap)
    (hTailMass : tailMass ≤ 2 * lambda)
    (hHighGap :
      gapConstant * lambda ^ 8 * localGap ≤ highGap)
    (hWeylTail :
      4 * residueMass * highGap * correction ≤
        localGap * tailMass) :
    correction ≤
      1 / (2 * residueMass * gapConstant * lambda ^ 7) := by
  have hScaled := parsevalLambdaSevenCertificate
    correction residueMass gapConstant lambda localGap highGap tailMass
    hCorrection hResidue hGapConstant hLambda hLocalGap
    hTailMass hHighGap hWeylTail
  have hDen : 0 < 2 * residueMass * gapConstant * lambda ^ 7 := by positivity
  exact (le_div_iff₀ hDen).2 (by simpa [mul_assoc] using hScaled)

end RiemannCvs.ParsevalTailRate
