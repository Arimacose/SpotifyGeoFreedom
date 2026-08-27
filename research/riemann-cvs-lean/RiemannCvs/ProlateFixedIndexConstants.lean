import Mathlib

/-!
# Fixed-index prolate separation constants

This module checks the rational arithmetic in the Fuchs fixed-index ratios used
for the `(0,4,8)` and `(2,6,10)` Fourier classes.  The Fuchs asymptotic itself is
an external analytic theorem; only its coefficient ratios are formalized here.
-/

namespace RiemannCvs.ProlateFixedIndexConstants

/-- Coefficient ratio `A_8 / A_4` for
`A_n = 2^(3n) / n!`. -/
theorem defectEightOverFour :
    ((2 : ℝ) ^ 24 / 40320) /
      ((2 : ℝ) ^ 12 / 24) = 256 / 105 := by
  norm_num

/-- Coefficient ratio `A_10 / A_6`. -/
theorem defectTenOverSix :
    ((2 : ℝ) ^ 30 / 3628800) /
      ((2 : ℝ) ^ 18 / 720) = 256 / 315 := by
  norm_num

/-- Reciprocal ratio used in the `+1` high-pole correction. -/
theorem defectFourOverEight :
    ((105 : ℝ) / 256) = 1 / (256 / 105) := by
  norm_num

/-- Reciprocal ratio used in the `-1` high-pole correction. -/
theorem defectSixOverTen :
    ((315 : ℝ) / 256) = 1 / (256 / 315) := by
  norm_num

/-- Converting `c = 2*pi*lambda^2` sends `c^4` to
`16*pi^4*lambda^8`. -/
theorem bandwidthFourthPower
    (lambda : ℝ) :
    (2 * Real.pi * lambda ^ 2) ^ 4 =
      16 * Real.pi ^ 4 * lambda ^ 8 := by
  ring

/-- Limiting low-residue mass in the Fourier `+1` class. -/
theorem plusResidueMass :
    Real.sqrt 2 * (1 + 3 / 8) =
      11 * Real.sqrt 2 / 8 := by
  ring

/-- Limiting low-residue mass in the Fourier `-1` class. -/
theorem minusResidueMass :
    Real.sqrt 2 * (1 / 2 + 5 / 16) =
      13 * Real.sqrt 2 / 16 := by
  ring

/-- Simplification of the asymptotic `+1` correction constant. -/
theorem plusCorrectionConstant :
    (105 : ℝ) /
        (8192 * (11 * Real.sqrt 2 / 8) * Real.pi ^ 4) =
      105 / (11264 * Real.sqrt 2 * Real.pi ^ 4) := by
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hsqrt, hpi]
  ring

/-- Simplification of the asymptotic `-1` correction constant. -/
theorem minusCorrectionConstant :
    (315 : ℝ) /
        (8192 * (13 * Real.sqrt 2 / 16) * Real.pi ^ 4) =
      315 / (6656 * Real.sqrt 2 * Real.pi ^ 4) := by
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hsqrt, hpi]
  ring

end RiemannCvs.ProlateFixedIndexConstants
