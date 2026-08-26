import Mathlib

/-!
# Low Hermite boundary residues

For normalized even Hermite functions, the squared value at the origin relative
to the ground Hermite function is

`(2k)! / (2^(2k) (k!)^2)`.

This file checks the low-index rational constants used in the constrained
prolate secular roots.  The analytic convergence of prolate residues to these
Hermite residues is not asserted here.
-/

namespace RiemannCvs.HermiteResidues

/-- Relative residue of `h₂`. -/
theorem residueTwo :
    ((2 : ℝ) / (2 ^ 2 * (1 : ℝ) ^ 2)) = 1 / 2 := by
  norm_num

/-- Relative residue of `h₄`. -/
theorem residueFour :
    ((24 : ℝ) / (2 ^ 4 * (2 : ℝ) ^ 2)) = 3 / 8 := by
  norm_num

/-- Relative residue of `h₆`. -/
theorem residueSix :
    ((720 : ℝ) / (2 ^ 6 * (6 : ℝ) ^ 2)) = 5 / 16 := by
  norm_num

/-- Relative residue of `h₈`. -/
theorem residueEight :
    ((40320 : ℝ) / (2 ^ 8 * (24 : ℝ) ^ 2)) = 35 / 128 := by
  norm_num

/-- Relative residue of `h₁₀`. -/
theorem residueTen :
    ((3628800 : ℝ) / (2 ^ 10 * (120 : ℝ) ^ 2)) = 63 / 256 := by
  norm_num

/-- First constrained-root weight in the Fourier `+1` class. -/
theorem firstPlusWeight :
    (1 : ℝ) / (1 + 3 / 8) = 8 / 11 := by
  norm_num

/-- First constrained-root weight in the Fourier `-1` class. -/
theorem firstMinusWeight :
    ((1 / 2 : ℝ) / (1 / 2 + 5 / 16)) = 8 / 13 := by
  norm_num

/-- Second constrained-root weight in the Fourier `+1` class. -/
theorem secondPlusWeight :
    ((1 + 3 / 8 : ℝ) / (1 + 3 / 8 + 35 / 128)) = 176 / 211 := by
  norm_num

/-- Second constrained-root weight in the Fourier `-1` class. -/
theorem secondMinusWeight :
    ((1 / 2 + 5 / 16 : ℝ) /
      (1 / 2 + 5 / 16 + 63 / 256)) = 208 / 271 := by
  norm_num

/-- Ratio of the two first constrained-root weights. -/
theorem firstWeightRatio :
    ((8 / 11 : ℝ) / (8 / 13)) = 13 / 11 := by
  norm_num

end RiemannCvs.HermiteResidues
