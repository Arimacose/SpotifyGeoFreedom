import Mathlib

/-!
# Low/high block transfer for parity separation

This file isolates a missing logical step in the prolate-to-Weil program.
Control of a fixed low-mode block alone does not lower-bound the ground state of
an entire parity sector: the orthogonal complement and the low/high coupling
must also be controlled.  The lemmas below give an interval-friendly Schur
complement certificate.

The intended scale is:

* the even trial energy is `O(λ⁻⁴)` in units of the lowest odd reference energy;
* the low odd block has a fixed positive lower bound `m`;
* the high odd complement is bounded below by `G * λ⁸`;
* the normalized low/high coupling is `k = o(λ⁴)`.

No analytic estimate for the Weil form is asserted here.  Every such estimate
appears explicitly as a hypothesis.
-/

namespace RiemannCvs.BlockGapTransfer

/-- Positivity of a real symmetric two-by-two quadratic form from its first
pivot and determinant.  This multiplication-only version is convenient for
rational or interval certificates. -/
theorem twoByTwoFormNonnegative
    (A B k u v : ℝ)
    (hA : 0 < A)
    (hdet : k ^ 2 ≤ A * B) :
    0 ≤ A * u ^ 2 + B * v ^ 2 - 2 * k * u * v := by
  have hv : 0 ≤ v ^ 2 := sq_nonneg v
  have hdetScaled : k ^ 2 * v ^ 2 ≤ (A * B) * v ^ 2 :=
    mul_le_mul_of_nonneg_right hdet hv
  have hsquare : 0 ≤ (A * u - k * v) ^ 2 := sq_nonneg (A * u - k * v)
  nlinarith

/-- A Schur-complement lower bound for a low/high decomposition.

If `a` lower-bounds the low block, `gamma` lower-bounds the high block and `k`
bounds the coupling, then any `mu` below both blocks is a global lower bound as
soon as the two-by-two determinant condition holds. -/
theorem blockLowerBound
    (q x y a gamma k mu : ℝ)
    (hLowPivot : 0 < a - mu)
    (hdet : k ^ 2 ≤ (a - mu) * (gamma - mu))
    (hq : a * x ^ 2 + gamma * y ^ 2 - 2 * k * x * y ≤ q) :
    mu * (x ^ 2 + y ^ 2) ≤ q := by
  have hform := twoByTwoFormNonnegative
    (a - mu) (gamma - mu) k x y hLowPivot hdet
  nlinarith

/-- At the natural prolate scales, a `λ⁸` high-block gap absorbs a coupling
whose square is smaller than the corresponding determinant budget. -/
theorem lambdaEightBlockLowerBound
    (q e x y m G k lambda : ℝ)
    (he : 0 < e)
    (hm : 0 < m)
    (hdet :
      k ^ 2 ≤ (m / 2) * (G * lambda ^ 8 - m / 2))
    (hq :
      e * (m * x ^ 2 + G * lambda ^ 8 * y ^ 2 - 2 * k * x * y) ≤ q) :
    e * (m / 2) * (x ^ 2 + y ^ 2) ≤ q := by
  have hpivot : 0 < m - m / 2 := by nlinarith
  have hbase :
      (m / 2) * (x ^ 2 + y ^ 2) ≤
        m * x ^ 2 + G * lambda ^ 8 * y ^ 2 - 2 * k * x * y := by
    exact blockLowerBound
      (m * x ^ 2 + G * lambda ^ 8 * y ^ 2 - 2 * k * x * y)
      x y m (G * lambda ^ 8) k (m / 2)
      hpivot hdet le_rfl
  have hscaled := mul_le_mul_of_nonneg_left hbase (le_of_lt he)
  nlinarith

/-- A division-free sufficient condition for the determinant hypothesis in
`lambdaEightBlockLowerBound`.

The condition is equivalent to saying that the normalized low/high coupling is
strictly below the geometric mean of the low margin and the `λ⁸` high gap. -/
theorem lambdaEightDeterminantFromCouplingBudget
    (m G k lambda : ℝ)
    (hbudget : 2 * k ^ 2 + m ^ 2 / 2 ≤ m * G * lambda ^ 8) :
    k ^ 2 ≤ (m / 2) * (G * lambda ^ 8 - m / 2) := by
  nlinarith

/-- Full parity-separation certificate.

The odd vector is normalized by `x² + y² = 1`.  The even upper bound is written
without division as `λ⁴ qPlus ≤ e M C`; the pure prolate input is represented by
the quartic margin `2 M C < m λ⁴`. -/
theorem quarticEvenOddSeparation
    (qPlus qMinus e x y m G k M C lambda : ℝ)
    (he : 0 < e)
    (hm : 0 < m)
    (hlambda : 0 < lambda)
    (hnorm : x ^ 2 + y ^ 2 = 1)
    (hOdd :
      e * (m * x ^ 2 + G * lambda ^ 8 * y ^ 2 - 2 * k * x * y) ≤ qMinus)
    (hdet :
      k ^ 2 ≤ (m / 2) * (G * lambda ^ 8 - m / 2))
    (hEvenScaled : lambda ^ 4 * qPlus ≤ e * (M * C))
    (hQuarticMargin : 2 * (M * C) < m * lambda ^ 4) :
    qPlus < qMinus := by
  have hOddLower := lambdaEightBlockLowerBound
    qMinus e x y m G k lambda he hm hdet hOdd
  rw [hnorm, mul_one] at hOddLower

  have hlambda4 : 0 < lambda ^ 4 := pow_pos hlambda 4
  have hmarginScaled := mul_lt_mul_of_pos_left hQuarticMargin he
  have hEvenStrictScaled :
      lambda ^ 4 * qPlus < lambda ^ 4 * (e * (m / 2)) := by
    nlinarith
  have hEven : qPlus < e * (m / 2) := by
    exact (mul_lt_mul_left hlambda4).mp hEvenStrictScaled
  exact lt_of_lt_of_le hEven hOddLower

/-- Same conclusion using the division-free coupling budget directly. -/
theorem quarticEvenOddSeparationFromCouplingBudget
    (qPlus qMinus e x y m G k M C lambda : ℝ)
    (he : 0 < e)
    (hm : 0 < m)
    (hlambda : 0 < lambda)
    (hnorm : x ^ 2 + y ^ 2 = 1)
    (hOdd :
      e * (m * x ^ 2 + G * lambda ^ 8 * y ^ 2 - 2 * k * x * y) ≤ qMinus)
    (hCouplingBudget : 2 * k ^ 2 + m ^ 2 / 2 ≤ m * G * lambda ^ 8)
    (hEvenScaled : lambda ^ 4 * qPlus ≤ e * (M * C))
    (hQuarticMargin : 2 * (M * C) < m * lambda ^ 4) :
    qPlus < qMinus := by
  have hdet := lambdaEightDeterminantFromCouplingBudget
    m G k lambda hCouplingBudget
  exact quarticEvenOddSeparation
    qPlus qMinus e x y m G k M C lambda
    he hm hlambda hnorm hOdd hdet hEvenScaled hQuarticMargin

end RiemannCvs.BlockGapTransfer
