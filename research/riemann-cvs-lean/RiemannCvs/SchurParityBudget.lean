import Mathlib

/-!
# Schur-complement parity budgets

This file isolates the finite-dimensional inequalities needed after splitting a
self-adjoint operator into a low prolate block and a high-mode complement.

The intended analytic application supplies:

* an even/odd low-block margin of order `lambda⁻⁴`;
* Schur or secular corrections of order `lambda⁻⁷`;
* positive complement gaps.

Only the scalar order-theoretic consequences are proved here.  No assertion
about the Weil operator, prolate asymptotics, or the Riemann hypothesis is hidden
in the hypotheses.
-/

namespace RiemannCvs.SchurParityBudget

/-- A direct Schur-corrected parity certificate.

The upper and lower estimates may come from Rayleigh--Ritz and a Schur/Temple
lower bound respectively. -/
theorem schurCorrectedParity
    (qPlus qMinus basePlus baseMinus corrPlus corrMinus : ℝ)
    (hPlus : qPlus ≤ basePlus + corrPlus)
    (hMinus : baseMinus - corrMinus ≤ qMinus)
    (hMargin : basePlus + corrPlus < baseMinus - corrMinus) :
    qPlus < qMinus := by
  exact lt_of_le_of_lt hPlus (lt_of_lt_of_le hMargin hMinus)

/-- Convert a division-free Schur budget into the usual corrected low-block
margin.  This formulation is convenient for exact rational or interval
certificates.

The product hypothesis is equivalent to

`epsPlusSq / gapPlus + epsMinusSq / gapMinus < baseMinus - basePlus`

when the two complement gaps are positive. -/
theorem productSchurMargin
    (basePlus baseMinus epsPlusSq epsMinusSq gapPlus gapMinus : ℝ)
    (hGapPlus : 0 < gapPlus)
    (hGapMinus : 0 < gapMinus)
    (hProductMargin :
      gapPlus * gapMinus * (baseMinus - basePlus) >
        gapMinus * epsPlusSq + gapPlus * epsMinusSq) :
    basePlus + epsPlusSq / gapPlus <
      baseMinus - epsMinusSq / gapMinus := by
  have hProd : 0 < gapPlus * gapMinus := mul_pos hGapPlus hGapMinus
  have hIdentity :
      (epsPlusSq / gapPlus + epsMinusSq / gapMinus) *
          (gapPlus * gapMinus) =
        gapMinus * epsPlusSq + gapPlus * epsMinusSq := by
    field_simp [ne_of_gt hGapPlus, ne_of_gt hGapMinus]
    ring
  have hScaled :
      (epsPlusSq / gapPlus + epsMinusSq / gapMinus) *
          (gapPlus * gapMinus) <
        (baseMinus - basePlus) * (gapPlus * gapMinus) := by
    rw [hIdentity]
    nlinarith [hProductMargin]
  have hUnscaled :
      epsPlusSq / gapPlus + epsMinusSq / gapMinus <
        baseMinus - basePlus := by
    exact (mul_lt_mul_right hProd).mp hScaled
  nlinarith

/-- Full division-free Schur-complement parity certificate.

`epsPlusSq` and `epsMinusSq` are squared coupling bounds, while `gapPlus` and
`gapMinus` are lower bounds for the corresponding high-mode complement gaps. -/
theorem productSchurParity
    (qPlus qMinus basePlus baseMinus epsPlusSq epsMinusSq
      gapPlus gapMinus : ℝ)
    (hGapPlus : 0 < gapPlus)
    (hGapMinus : 0 < gapMinus)
    (hPlus : qPlus ≤ basePlus + epsPlusSq / gapPlus)
    (hMinus : baseMinus - epsMinusSq / gapMinus ≤ qMinus)
    (hProductMargin :
      gapPlus * gapMinus * (baseMinus - basePlus) >
        gapMinus * epsPlusSq + gapPlus * epsMinusSq) :
    qPlus < qMinus := by
  have hMargin := productSchurMargin
    basePlus baseMinus epsPlusSq epsMinusSq gapPlus gapMinus
    hGapPlus hGapMinus hProductMargin
  exact schurCorrectedParity
    qPlus qMinus basePlus baseMinus
    (epsPlusSq / gapPlus) (epsMinusSq / gapMinus)
    hPlus hMinus hMargin

/-- A multiplication-only certificate showing that a `lambda⁻⁷` correction
cannot destroy a `lambda⁻⁴` parity signal once the explicit finite-scale margin
is positive.

After division by `lambda⁷ * oddScale`, the assumptions correspond to

`qPlus / oddScale ≤ C4 / lambda⁴ + C7Plus / lambda⁷`

and

`qMinus / oddScale ≥ m - C7Minus / lambda⁷`.
-/
theorem quarticSignalSeventhError
    (qPlus qMinus oddScale lambda C4 C7Plus C7Minus m : ℝ)
    (hLambda : 0 < lambda)
    (hOddScale : 0 < oddScale)
    (hPlusScaled :
      lambda ^ 7 * qPlus ≤
        (C4 * lambda ^ 3 + C7Plus) * oddScale)
    (hMinusScaled :
      (m * lambda ^ 7 - C7Minus) * oddScale ≤
        lambda ^ 7 * qMinus)
    (hMargin :
      C4 * lambda ^ 3 + C7Plus + C7Minus <
        m * lambda ^ 7) :
    qPlus < qMinus := by
  have hLambdaSeven : 0 < lambda ^ 7 := pow_pos hLambda 7
  have hMiddle :
      (C4 * lambda ^ 3 + C7Plus) * oddScale <
        (m * lambda ^ 7 - C7Minus) * oddScale := by
    have h := mul_lt_mul_of_pos_right hMargin hOddScale
    nlinarith
  have hScaled : lambda ^ 7 * qPlus < lambda ^ 7 * qMinus :=
    lt_of_le_of_lt hPlusScaled (lt_of_lt_of_le hMiddle hMinusScaled)
  exact (mul_lt_mul_left hLambdaSeven).mp hScaled

/-- A convenient sufficient condition for the preceding margin: if `lambda ≥ 1`
and the combined correction constant is dominated by the residual seventh-power
budget, then the strict parity ordering follows. -/
theorem quarticSignalSeventhErrorOfBudget
    (qPlus qMinus oddScale lambda C4 C7Plus C7Minus m : ℝ)
    (hLambda : 1 ≤ lambda)
    (hOddScale : 0 < oddScale)
    (hPlusScaled :
      lambda ^ 7 * qPlus ≤
        (C4 * lambda ^ 3 + C7Plus) * oddScale)
    (hMinusScaled :
      (m * lambda ^ 7 - C7Minus) * oddScale ≤
        lambda ^ 7 * qMinus)
    (hBudget :
      C4 * lambda ^ 3 + C7Plus + C7Minus <
        m * lambda ^ 7) :
    qPlus < qMinus := by
  have hLambdaPos : 0 < lambda := lt_of_lt_of_le zero_lt_one hLambda
  exact quarticSignalSeventhError
    qPlus qMinus oddScale lambda C4 C7Plus C7Minus m
    hLambdaPos hOddScale hPlusScaled hMinusScaled hBudget

end RiemannCvs.SchurParityBudget
