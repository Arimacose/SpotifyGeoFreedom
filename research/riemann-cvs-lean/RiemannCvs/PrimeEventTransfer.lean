import Mathlib

/-!
# Prime-event transfer identities

This file isolates the algebraic core of the reduced-resolvent jump formula.
The analytic perturbation theorem supplying the hypotheses is intentionally
kept outside this file. Once one-sided eigenvector derivatives satisfy

`x'± = -R (Q'± x)`

and a prime event has rank-one velocity jump

`Q'+ - Q'- = -a · v vᵀ`,

the conclusions below are purely finite-dimensional linear algebra.
-/

namespace RiemannCvs.PrimeEventTransfer

section LinearAlgebra

variable {𝕜 V : Type*}
variable [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- Algebraic core of the eigenvector derivative jump.

`y` denotes `Q'₋ x`, `c` denotes the scalar pairing `vᵀx`, and `R` is the
reduced resolvent. -/
theorem derivativeJump
    (R : V →ₗ[𝕜] V) (y v dxPlus dxMinus : V) (a c : 𝕜)
    (hPlus : dxPlus = -R (y - (a * c) • v))
    (hMinus : dxMinus = -R y) :
    dxPlus - dxMinus = (a * c) • R v := by
  rw [hPlus, hMinus, R.map_sub, R.map_smul]
  abel

/-- Apply a linear functional to `derivativeJump` and divide by a nonzero
normalizing value. This is the finite-dimensional logarithmic-transfer
identity before differentiating in the spectral variable. -/
theorem functionalDerivativeJump
    (R : V →ₗ[𝕜] V) (ell : V →ₗ[𝕜] 𝕜)
    (x y v dxPlus dxMinus : V) (a c : 𝕜)
    (hEll : ell x ≠ 0)
    (hPlus : dxPlus = -R (y - (a * c) • v))
    (hMinus : dxMinus = -R y) :
    ell dxPlus / ell x - ell dxMinus / ell x
      = (a * c) * ell (R v) / ell x := by
  have hVec := derivativeJump R y v dxPlus dxMinus a c hPlus hMinus
  calc
    ell dxPlus / ell x - ell dxMinus / ell x
        = (ell dxPlus - ell dxMinus) / ell x := by ring
    _ = ell (dxPlus - dxMinus) / ell x := by rw [map_sub]
    _ = ell ((a * c) • R v) / ell x := by rw [hVec]
    _ = (a * c) * ell (R v) / ell x := by simp [smul_eq_mul]

/-- A statement-shaped version of the prime-event functional transfer once the
vector jump has already been established. -/
theorem rankOneFunctionalTransfer
    (R : V →ₗ[𝕜] V) (ell : V →ₗ[𝕜] 𝕜)
    (x v dxJump : V) (a c : 𝕜)
    (hEll : ell x ≠ 0)
    (hJump : dxJump = (a * c) • R v) :
    ell dxJump / ell x = (a * c) * ell (R v) / ell x := by
  rw [hJump, map_smul]
  simp [smul_eq_mul]

end LinearAlgebra

section Arithmetic

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- The algebraic cancellation behind

`(1/2) * u * [2 Λ / (sqrt(q) u)] = Λ / sqrt(q)`.

The exponential factor in the Euler/Laplace bridge is analytic rather than
algebraic and is therefore not included here. -/
theorem halfWeightCancel (Λ sqrtq u a : 𝕜)
    (hu : u ≠ 0) (hsqrt : sqrtq ≠ 0)
    (ha : a = 2 * Λ / (sqrtq * u)) :
    (1 / 2 : 𝕜) * u * a = Λ / sqrtq := by
  rw [ha]
  field_simp [hu, hsqrt]
  ring

end Arithmetic

end RiemannCvs.PrimeEventTransfer
