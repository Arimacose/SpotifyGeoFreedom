import Mathlib

/-!
# Projection of approximate inversion parity

The map `𝓔` sends exact additive Fourier `±1` classes to exact multiplicative
inversion parity.  Finite prolate modes have a small Fourier leakage, so their
images have only approximate inversion parity.  The correct trial vectors for
the Weil even and odd sectors are therefore the exact projections

`P₊ w = (w + J w) / 2`,  `P₋ w = (w - J w) / 2`.

This file proves the algebraic, norm, and quadratic-form identities needed to
replace an approximate-parity vector by its exact sector projection without
losing the scale of a small parity defect.
-/

namespace RiemannCvs.ParityProjection

section Algebra

variable {W : Type*}
variable [AddCommGroup W] [Module ℝ W]

/-- Projection onto the `+1` eigenspace of an involution. -/
def evenPart (J : W →ₗ[ℝ] W) (w : W) : W :=
  (1 / 2 : ℝ) • (w + J w)

/-- Projection onto the `-1` eigenspace of an involution. -/
def oddPart (J : W →ₗ[ℝ] W) (w : W) : W :=
  (1 / 2 : ℝ) • (w - J w)

/-- The two parity projections sum to the original vector. -/
theorem evenPart_add_oddPart
    (J : W →ₗ[ℝ] W) (w : W) :
    evenPart J w + oddPart J w = w := by
  unfold evenPart oddPart
  module

/-- If `J² = 1`, the even projection is fixed by `J`. -/
theorem map_evenPart
    (J : W →ₗ[ℝ] W) (w : W)
    (hJ : J (J w) = w) :
    J (evenPart J w) = evenPart J w := by
  unfold evenPart
  rw [map_smul, map_add, hJ]
  module

/-- If `J² = 1`, the odd projection is negated by `J`. -/
theorem map_oddPart
    (J : W →ₗ[ℝ] W) (w : W)
    (hJ : J (J w) = w) :
    J (oddPart J w) = -oddPart J w := by
  unfold oddPart
  rw [map_smul, map_sub, hJ]
  module

/-- Removing the even projection leaves precisely the odd projection. -/
theorem sub_evenPart
    (J : W →ₗ[ℝ] W) (w : W) :
    w - evenPart J w = oddPart J w := by
  have h := evenPart_add_oddPart J w
  module

/-- Removing the odd projection leaves precisely the even projection. -/
theorem sub_oddPart
    (J : W →ₗ[ℝ] W) (w : W) :
    w - oddPart J w = evenPart J w := by
  have h := evenPart_add_oddPart J w
  module

end Algebra

section Norm

variable {W : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The wrong-parity norm for an intended even vector is exactly half of its
inversion-evenness defect. -/
theorem norm_oddPart
    (J : W →ₗ[ℝ] W) (w : W) :
    ‖oddPart J w‖ = (1 / 2 : ℝ) * ‖w - J w‖ := by
  unfold oddPart
  rw [norm_smul]
  norm_num [Real.norm_eq_abs]

/-- The wrong-parity norm for an intended odd vector is exactly half of its
inversion-oddness defect. -/
theorem norm_evenPart
    (J : W →ₗ[ℝ] W) (w : W) :
    ‖evenPart J w‖ = (1 / 2 : ℝ) * ‖w + J w‖ := by
  unfold evenPart
  rw [norm_smul]
  norm_num [Real.norm_eq_abs]

/-- Squared version of `norm_oddPart`. -/
theorem normSq_oddPart
    (J : W →ₗ[ℝ] W) (w : W) :
    ‖oddPart J w‖ ^ 2 = (1 / 4 : ℝ) * ‖w - J w‖ ^ 2 := by
  rw [norm_oddPart]
  ring

/-- Squared version of `norm_evenPart`. -/
theorem normSq_evenPart
    (J : W →ₗ[ℝ] W) (w : W) :
    ‖evenPart J w‖ ^ 2 = (1 / 4 : ℝ) * ‖w + J w‖ ^ 2 := by
  rw [norm_evenPart]
  ring

end Norm

section QuadraticForm

variable {W : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- An inversion-invariant bilinear form has zero mixed term between the exact
`+1` and `-1` projections. -/
theorem even_odd_cross_zero
    (J : W →ₗ[ℝ] W)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (w : W)
    (hJ : J (J w) = w)
    (hInvariant : ∀ x y, B (J x) (J y) = B x y) :
    B (evenPart J w) (oddPart J w) = 0 := by
  have h := hInvariant (evenPart J w) (oddPart J w)
  rw [map_evenPart J w hJ, map_oddPart J w hJ] at h
  simp only [map_neg] at h
  linarith

/-- The opposite mixed term also vanishes; symmetry of `B` is not needed. -/
theorem odd_even_cross_zero
    (J : W →ₗ[ℝ] W)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (w : W)
    (hJ : J (J w) = w)
    (hInvariant : ∀ x y, B (J x) (J y) = B x y) :
    B (oddPart J w) (evenPart J w) = 0 := by
  have h := hInvariant (oddPart J w) (evenPart J w)
  rw [map_oddPart J w hJ, map_evenPart J w hJ] at h
  simp only [LinearMap.map_neg] at h
  linarith

/-- Exact quadratic-energy splitting into the two inversion sectors. -/
theorem energy_split
    (J : W →ₗ[ℝ] W)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (w : W)
    (hJ : J (J w) = w)
    (hInvariant : ∀ x y, B (J x) (J y) = B x y) :
    B w w =
      B (evenPart J w) (evenPart J w) +
        B (oddPart J w) (oddPart J w) := by
  have hdecomp := evenPart_add_oddPart J w
  have hcross₁ := even_odd_cross_zero J B w hJ hInvariant
  have hcross₂ := odd_even_cross_zero J B w hJ hInvariant
  calc
    B w w = B (evenPart J w + oddPart J w)
        (evenPart J w + oddPart J w) := by rw [hdecomp]
    _ = B (evenPart J w) (evenPart J w) +
        B (oddPart J w) (oddPart J w) := by
      simp [map_add, hcross₁, hcross₂]

/-- If the form is bounded below by `-C‖·‖²` on the wrong-parity component,
projecting an approximate-even vector to the exact even sector costs at most a
quarter of `C` times the squared parity defect. -/
theorem evenProjectionEnergyUpper
    (J : W →ₗ[ℝ] W)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (w : W) (C : ℝ)
    (hJ : J (J w) = w)
    (hInvariant : ∀ x y, B (J x) (J y) = B x y)
    (hOddLower :
      -(C * ‖oddPart J w‖ ^ 2) ≤ B (oddPart J w) (oddPart J w)) :
    B (evenPart J w) (evenPart J w) ≤
      B w w + (C / 4) * ‖w - J w‖ ^ 2 := by
  have hsplit := energy_split J B w hJ hInvariant
  have hnorm := normSq_oddPart J w
  rw [hnorm] at hOddLower
  nlinarith

/-- Symmetric statement for projecting an approximate-odd vector. -/
theorem oddProjectionEnergyUpper
    (J : W →ₗ[ℝ] W)
    (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (w : W) (C : ℝ)
    (hJ : J (J w) = w)
    (hInvariant : ∀ x y, B (J x) (J y) = B x y)
    (hEvenLower :
      -(C * ‖evenPart J w‖ ^ 2) ≤ B (evenPart J w) (evenPart J w)) :
    B (oddPart J w) (oddPart J w) ≤
      B w w + (C / 4) * ‖w + J w‖ ^ 2 := by
  have hsplit := energy_split J B w hJ hInvariant
  have hnorm := normSq_evenPart J w
  rw [hnorm] at hEvenLower
  nlinarith

end QuadraticForm

end RiemannCvs.ParityProjection
