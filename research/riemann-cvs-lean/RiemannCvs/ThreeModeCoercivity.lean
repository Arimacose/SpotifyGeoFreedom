import Mathlib

/-!
# Three-mode coercivity certificates

This file formalizes a quantitative certificate for a real symmetric 3-by-3
Gram matrix.  The intended analytic application is a normalized exterior-tail
matrix on one of the fixed prolate mode families `{0,4,8}` or `{2,6,10}`.

The certificate does not require the matrix to converge to the identity.  It is
enough that its diagonal entries dominate the sum of the two off-diagonal
bounds in each row.  This is well suited to directed interval arithmetic: six
entry enclosures imply a uniform lower and upper quadratic-form bound.

No prolate asymptotic or Weil-form assertion is hidden here.
-/

namespace RiemannCvs.ThreeModeCoercivity

/-- A bounded scalar coefficient controls one real cross term from below. -/
theorem crossTermLower
    (g x y eps : ℝ)
    (heps : 0 ≤ eps)
    (hg : |g| ≤ eps) :
    -eps * (x ^ 2 + y ^ 2) ≤ 2 * g * x * y := by
  obtain ⟨hglower, hgupper⟩ := abs_le.mp hg
  by_cases hxy : 0 ≤ x * y
  · have hcoeff : -2 * eps * (x * y) ≤ 2 * g * (x * y) := by
      nlinarith
    have hsquare := sq_nonneg (x - y)
    nlinarith
  · have hxy_nonpos : x * y ≤ 0 := le_of_not_ge hxy
    have hcoeff : 2 * eps * (x * y) ≤ 2 * g * (x * y) := by
      nlinarith
    have hsquare := sq_nonneg (x + y)
    nlinarith

/-- The matching upper bound for a real cross term. -/
theorem crossTermUpper
    (g x y eps : ℝ)
    (heps : 0 ≤ eps)
    (hg : |g| ≤ eps) :
    2 * g * x * y ≤ eps * (x ^ 2 + y ^ 2) := by
  have hneg : |-g| ≤ eps := by simpa using hg
  have h := crossTermLower (-g) x y eps heps hneg
  nlinarith

/-- Strict diagonal dominance gives a uniform lower quadratic-form bound.

The represented matrix is

```
[a   b   d]
[b   c   e]
[d   e   f].
```
-/
theorem lowerBoundOfDiagonalDominance
    (a b c d e f x y z mu eps : ℝ)
    (heps : 0 ≤ eps)
    (ha : mu + 2 * eps ≤ a)
    (hc : mu + 2 * eps ≤ c)
    (hf : mu + 2 * eps ≤ f)
    (hb : |b| ≤ eps)
    (hd : |d| ≤ eps)
    (he : |e| ≤ eps) :
    mu * (x ^ 2 + y ^ 2 + z ^ 2) ≤
      a * x ^ 2 + c * y ^ 2 + f * z ^ 2 +
        2 * b * x * y + 2 * d * x * z + 2 * e * y * z := by
  have hxy := crossTermLower b x y eps heps hb
  have hxz := crossTermLower d x z eps heps hd
  have hyz := crossTermLower e y z eps heps he
  have hx2 := sq_nonneg x
  have hy2 := sq_nonneg y
  have hz2 := sq_nonneg z
  nlinarith

/-- A matching uniform upper bound. -/
theorem upperBoundOfEntryControl
    (a b c d e f x y z M eps : ℝ)
    (heps : 0 ≤ eps)
    (ha : a ≤ M - 2 * eps)
    (hc : c ≤ M - 2 * eps)
    (hf : f ≤ M - 2 * eps)
    (hb : |b| ≤ eps)
    (hd : |d| ≤ eps)
    (he : |e| ≤ eps) :
    a * x ^ 2 + c * y ^ 2 + f * z ^ 2 +
        2 * b * x * y + 2 * d * x * z + 2 * e * y * z ≤
      M * (x ^ 2 + y ^ 2 + z ^ 2) := by
  have hxy := crossTermUpper b x y eps heps hb
  have hxz := crossTermUpper d x z eps heps hd
  have hyz := crossTermUpper e y z eps heps he
  have hx2 := sq_nonneg x
  have hy2 := sq_nonneg y
  have hz2 := sq_nonneg z
  nlinarith

/-- Six interval-style entry bounds yield two-sided coercivity on the whole
three-dimensional mode space. -/
theorem twoSidedThreeModeCertificate
    (a b c d e f x y z mu M eps : ℝ)
    (heps : 0 ≤ eps)
    (haLower : mu + 2 * eps ≤ a)
    (hcLower : mu + 2 * eps ≤ c)
    (hfLower : mu + 2 * eps ≤ f)
    (haUpper : a ≤ M - 2 * eps)
    (hcUpper : c ≤ M - 2 * eps)
    (hfUpper : f ≤ M - 2 * eps)
    (hb : |b| ≤ eps)
    (hd : |d| ≤ eps)
    (he : |e| ≤ eps) :
    mu * (x ^ 2 + y ^ 2 + z ^ 2) ≤
        a * x ^ 2 + c * y ^ 2 + f * z ^ 2 +
          2 * b * x * y + 2 * d * x * z + 2 * e * y * z ∧
      a * x ^ 2 + c * y ^ 2 + f * z ^ 2 +
          2 * b * x * y + 2 * d * x * z + 2 * e * y * z ≤
        M * (x ^ 2 + y ^ 2 + z ^ 2) := by
  exact ⟨
    lowerBoundOfDiagonalDominance a b c d e f x y z mu eps
      heps haLower hcLower hfLower hb hd he,
    upperBoundOfEntryControl a b c d e f x y z M eps
      heps haUpper hcUpper hfUpper hb hd he
  ⟩

/-- Positive diagonal-dominance margin implies strict positivity away from the
zero vector. -/
theorem positiveDefiniteOfDiagonalDominance
    (a b c d e f x y z mu eps : ℝ)
    (hmu : 0 < mu)
    (heps : 0 ≤ eps)
    (ha : mu + 2 * eps ≤ a)
    (hc : mu + 2 * eps ≤ c)
    (hf : mu + 2 * eps ≤ f)
    (hb : |b| ≤ eps)
    (hd : |d| ≤ eps)
    (he : |e| ≤ eps)
    (hvec : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
    0 < a * x ^ 2 + c * y ^ 2 + f * z ^ 2 +
      2 * b * x * y + 2 * d * x * z + 2 * e * y * z := by
  have hlower := lowerBoundOfDiagonalDominance
    a b c d e f x y z mu eps heps ha hc hf hb hd he
  have hnormsq : 0 < x ^ 2 + y ^ 2 + z ^ 2 := by
    rcases hvec with hx | hy | hz
    · have := sq_pos_of_ne_zero hx
      nlinarith [sq_nonneg y, sq_nonneg z]
    · have := sq_pos_of_ne_zero hy
      nlinarith [sq_nonneg x, sq_nonneg z]
    · have := sq_pos_of_ne_zero hz
      nlinarith [sq_nonneg x, sq_nonneg y]
  nlinarith

end RiemannCvs.ThreeModeCoercivity
