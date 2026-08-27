import Mathlib

/-!
# Finite-section convergence and parity transfer

Suppose a self-adjoint operator is split into a retained finite block and a high
complement.  If the high complement has coercivity `gap` and the low/high
coupling is at most `epsilon`, completing the square gives the finite-section
error scale `2 * epsilon² / gap` for normalized vectors, provided the retained
low eigenvalue lies below the surviving high floor `gap / 2`.

This file records the scalar consequences used to transfer a certified finite
parity gap to the full operator.  The operator estimates remain external
analytic inputs.
-/

namespace RiemannCvs.FiniteSectionConvergence

/-- A variational upper bound together with the normalized Schur lower bound
places the full lowest value in a one-sided error interval below the finite
section. -/
theorem oneSectorFiniteSectionError
    (fullValue finiteValue gap epsilon : ℝ)
    (hVariational : fullValue ≤ finiteValue)
    (hSchur : finiteValue - 2 * epsilon ^ 2 / gap ≤ fullValue) :
    0 ≤ finiteValue - fullValue ∧
      finiteValue - fullValue ≤ 2 * epsilon ^ 2 / gap := by
  constructor <;> linarith

/-- Two finite parity blocks transfer their strict ordering to the full
operator once the finite margin dominates the two Schur errors. -/
theorem finiteGapTransfersToFull
    (fullPlus fullMinus finitePlus finiteMinus errPlus errMinus : ℝ)
    (hPlusUpper : fullPlus ≤ finitePlus)
    (hMinusLower : finiteMinus - errMinus ≤ fullMinus)
    (hMargin : finitePlus + errPlus < finiteMinus - errMinus) :
    fullPlus < fullMinus := by
  have h : finitePlus < finiteMinus - errMinus := by
    linarith
  exact lt_of_le_of_lt hPlusUpper (lt_of_lt_of_le h hMinusLower)

/-- Direct Schur-error specialization. -/
theorem schurFiniteGapTransfersToFull
    (fullPlus fullMinus finitePlus finiteMinus
      gapPlus gapMinus epsilonPlus epsilonMinus : ℝ)
    (hPlusUpper : fullPlus ≤ finitePlus)
    (hMinusLower :
      finiteMinus - 2 * epsilonMinus ^ 2 / gapMinus ≤ fullMinus)
    (hMargin :
      finitePlus + 2 * epsilonPlus ^ 2 / gapPlus <
        finiteMinus - 2 * epsilonMinus ^ 2 / gapMinus) :
    fullPlus < fullMinus := by
  exact finiteGapTransfersToFull
    fullPlus fullMinus finitePlus finiteMinus
    (2 * epsilonPlus ^ 2 / gapPlus)
    (2 * epsilonMinus ^ 2 / gapMinus)
    hPlusUpper hMinusLower hMargin

/-- Multiplication-only sufficient condition for the two Schur errors to fit
inside a certified finite parity margin.  This form is convenient for interval
arithmetic because it avoids divisions in the hypothesis. -/
theorem productFiniteGapMargin
    (finitePlus finiteMinus gapPlus gapMinus
      epsilonPlus epsilonMinus : ℝ)
    (hGapPlus : 0 < gapPlus)
    (hGapMinus : 0 < gapMinus)
    (hProductMargin :
      gapPlus * gapMinus * (finiteMinus - finitePlus) >
        2 * gapMinus * epsilonPlus ^ 2 +
          2 * gapPlus * epsilonMinus ^ 2) :
    finitePlus + 2 * epsilonPlus ^ 2 / gapPlus <
      finiteMinus - 2 * epsilonMinus ^ 2 / gapMinus := by
  have hProd : 0 < gapPlus * gapMinus := mul_pos hGapPlus hGapMinus
  have hIdentity :
      (2 * epsilonPlus ^ 2 / gapPlus +
          2 * epsilonMinus ^ 2 / gapMinus) *
          (gapPlus * gapMinus) =
        2 * gapMinus * epsilonPlus ^ 2 +
          2 * gapPlus * epsilonMinus ^ 2 := by
    field_simp [ne_of_gt hGapPlus, ne_of_gt hGapMinus]
    ring
  have hScaled :
      (2 * epsilonPlus ^ 2 / gapPlus +
          2 * epsilonMinus ^ 2 / gapMinus) *
          (gapPlus * gapMinus) <
        (finiteMinus - finitePlus) *
          (gapPlus * gapMinus) := by
    rw [hIdentity]
    nlinarith [hProductMargin]
  have hUnscaled :
      2 * epsilonPlus ^ 2 / gapPlus +
          2 * epsilonMinus ^ 2 / gapMinus <
        finiteMinus - finitePlus :=
    (mul_lt_mul_right hProd).mp hScaled
  nlinarith

/-- Complete division-free finite-to-full parity certificate. -/
theorem productFiniteGapTransfersToFull
    (fullPlus fullMinus finitePlus finiteMinus
      gapPlus gapMinus epsilonPlus epsilonMinus : ℝ)
    (hGapPlus : 0 < gapPlus)
    (hGapMinus : 0 < gapMinus)
    (hPlusUpper : fullPlus ≤ finitePlus)
    (hMinusLower :
      finiteMinus - 2 * epsilonMinus ^ 2 / gapMinus ≤ fullMinus)
    (hProductMargin :
      gapPlus * gapMinus * (finiteMinus - finitePlus) >
        2 * gapMinus * epsilonPlus ^ 2 +
          2 * gapPlus * epsilonMinus ^ 2) :
    fullPlus < fullMinus := by
  have hMargin := productFiniteGapMargin
    finitePlus finiteMinus gapPlus gapMinus
    epsilonPlus epsilonMinus
    hGapPlus hGapMinus hProductMargin
  exact schurFiniteGapTransfersToFull
    fullPlus fullMinus finitePlus finiteMinus
    gapPlus gapMinus epsilonPlus epsilonMinus
    hPlusUpper hMinusLower hMargin

end RiemannCvs.FiniteSectionConvergence
