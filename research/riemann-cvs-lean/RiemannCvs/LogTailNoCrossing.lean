import Mathlib

/-!
# Logarithmic high-mode tails and no-crossing budgets

A promising infinite-Galerkin bridge writes the high Fourier-mode part of the
finite Weil form as a growing diagonal symbol plus a bounded perturbation.  If
the diagonal lower bound is `highLevel`, the bounded perturbation has norm at
most `boundedPart`, and the spectral parameter is `mu`, then the available
complement gap is

`highLevel - boundedPart - mu`.

This file records the scalar budget needed to make the resulting Schur
correction smaller than a prescribed finite-dimensional parity margin.  The
operator decomposition and its analytic bounds are external inputs.
-/

namespace RiemannCvs.LogTailNoCrossing

/-- A Schur correction is at most one quarter of the target margin when its
multiplication-only budget holds. -/
theorem quarterMarginCorrection
    (correction couplingSq gap margin : ℝ)
    (hGap : 0 < gap)
    (hCorrection : correction ≤ couplingSq / gap)
    (hBudget : 4 * couplingSq ≤ margin * gap) :
    correction ≤ margin / 4 := by
  have hDiv : couplingSq / gap ≤ margin / 4 := by
    apply (div_le_iff₀ hGap).2
    nlinarith [hBudget]
  exact hCorrection.trans hDiv

/-- Explicit logarithmic-tail specialization.

The hypothesis `highLevel - boundedPart - mu > 0` is the complement gap, and
`4 * boundedPart² ≤ margin * gap` makes the Schur correction at most a quarter
of the parity margin. -/
theorem logarithmicTailQuarterMargin
    (correction highLevel boundedPart mu margin : ℝ)
    (hGap : 0 < highLevel - boundedPart - mu)
    (hCorrection :
      correction ≤
        boundedPart ^ 2 / (highLevel - boundedPart - mu))
    (hBudget :
      4 * boundedPart ^ 2 ≤
        margin * (highLevel - boundedPart - mu)) :
    correction ≤ margin / 4 := by
  exact quarterMarginCorrection
    correction (boundedPart ^ 2)
    (highLevel - boundedPart - mu) margin
    hGap hCorrection hBudget

/-- Two sector corrections, each bounded by one quarter of the unperturbed
margin, cannot close the parity gap. -/
theorem twoSectorNoCrossing
    (actualPlus actualMinus basePlus baseMinus corrPlus corrMinus margin : ℝ)
    (hMarginDef : margin = baseMinus - basePlus)
    (hMargin : 0 < margin)
    (hPlus : actualPlus ≤ basePlus + corrPlus)
    (hMinus : baseMinus - corrMinus ≤ actualMinus)
    (hCorrPlus : corrPlus ≤ margin / 4)
    (hCorrMinus : corrMinus ≤ margin / 4) :
    actualPlus < actualMinus := by
  rw [hMarginDef] at hMargin hCorrPlus hCorrMinus
  nlinarith

/-- Combined logarithmic-tail no-crossing certificate for two parity sectors. -/
theorem logarithmicTailNoCrossing
    (actualPlus actualMinus basePlus baseMinus
      corrPlus corrMinus highPlus highMinus
      boundedPlus boundedMinus muPlus muMinus margin : ℝ)
    (hMarginDef : margin = baseMinus - basePlus)
    (hMargin : 0 < margin)
    (hPlus : actualPlus ≤ basePlus + corrPlus)
    (hMinus : baseMinus - corrMinus ≤ actualMinus)
    (hGapPlus : 0 < highPlus - boundedPlus - muPlus)
    (hGapMinus : 0 < highMinus - boundedMinus - muMinus)
    (hSchurPlus :
      corrPlus ≤ boundedPlus ^ 2 /
        (highPlus - boundedPlus - muPlus))
    (hSchurMinus :
      corrMinus ≤ boundedMinus ^ 2 /
        (highMinus - boundedMinus - muMinus))
    (hBudgetPlus :
      4 * boundedPlus ^ 2 ≤
        margin * (highPlus - boundedPlus - muPlus))
    (hBudgetMinus :
      4 * boundedMinus ^ 2 ≤
        margin * (highMinus - boundedMinus - muMinus)) :
    actualPlus < actualMinus := by
  have hQuarterPlus := logarithmicTailQuarterMargin
    corrPlus highPlus boundedPlus muPlus margin
    hGapPlus hSchurPlus hBudgetPlus
  have hQuarterMinus := logarithmicTailQuarterMargin
    corrMinus highMinus boundedMinus muMinus margin
    hGapMinus hSchurMinus hBudgetMinus
  exact twoSectorNoCrossing
    actualPlus actualMinus basePlus baseMinus
    corrPlus corrMinus margin
    hMarginDef hMargin hPlus hMinus hQuarterPlus hQuarterMinus

end RiemannCvs.LogTailNoCrossing
