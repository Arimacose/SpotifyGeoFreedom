import Mathlib

/-!
# Continuation of a strict parity ordering

A numerical or asymptotic estimate at one parameter value does not by itself
control the parity ordering at other parameters.  The missing topological step
is elementary but important: two continuous eigenvalue branches can reverse
order only by meeting.

The theorems below isolate this step.  In the intended CvS application,
`evenEnergy` and `oddEnergy` are the lowest eigenvalue branches in the two
reflection sectors.  A rank-one Sylvester relation supplies the no-crossing
hypothesis once the relevant boundary overlaps are known to be nonzero.

No assertion about continuity of a concrete Weil family, simplicity of its
eigenvalues, or nonvanishing of its boundary overlaps is hidden here.
-/

namespace RiemannCvs.ParityOrderContinuation

open Set

/-- On a compact interval, a strict order between two continuous real-valued
functions persists if the functions never meet. -/
theorem strictOrderPersistsOnIcc
    (f g : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b))
    (hstart : f a < g a)
    (hneq : ∀ x ∈ Icc a b, f x ≠ g x) :
    ∀ x ∈ Icc a b, f x < g x := by
  intro x hx
  by_contra hnot
  have hcross : g x ≤ f x := le_of_not_gt hnot
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  obtain ⟨y, hy, heq⟩ :=
    isPreconnected_Icc.intermediate_value₂
      ha hx hf hg (le_of_lt hstart) hcross
  exact (hneq y hy) heq

/-- Half-line version anchored at the left endpoint. -/
theorem strictOrderPersistsOnIci
    (f g : ℝ → ℝ) (a : ℝ)
    (hf : ContinuousOn f (Ici a))
    (hg : ContinuousOn g (Ici a))
    (hstart : f a < g a)
    (hneq : ∀ x ∈ Ici a, f x ≠ g x) :
    ∀ x ∈ Ici a, f x < g x := by
  intro x hx
  have hax : a ≤ x := hx
  have hfIcc : ContinuousOn f (Icc a x) := by
    exact hf.mono (fun y hy => hy.1)
  have hgIcc : ContinuousOn g (Icc a x) := by
    exact hg.mono (fun y hy => hy.1)
  have hneqIcc : ∀ y ∈ Icc a x, f y ≠ g y := by
    intro y hy
    exact hneq y hy.1
  exact strictOrderPersistsOnIcc f g a x hax hfIcc hgIcc
    hstart hneqIcc x ⟨hax, le_rfl⟩

/-- Stronger half-line continuation theorem.  The strict ordering may be known
at any single anchor point `b ≥ a`, including an asymptotic or numerically
certified large parameter.  No-crossing then propagates the order both forward
and backward throughout the connected ray `Ici a`. -/
theorem strictOrderOnIciFromAnyAnchor
    (f g : ℝ → ℝ) (a b : ℝ)
    (hb : b ∈ Ici a)
    (hf : ContinuousOn f (Ici a))
    (hg : ContinuousOn g (Ici a))
    (hanchor : f b < g b)
    (hneq : ∀ x ∈ Ici a, f x ≠ g x) :
    ∀ x ∈ Ici a, f x < g x := by
  intro x hx
  by_contra hnot
  have hcross : g x ≤ f x := le_of_not_gt hnot
  obtain ⟨y, hy, heq⟩ :=
    isPreconnected_Ici.intermediate_value₂
      hb hx hf hg (le_of_lt hanchor) hcross
  exact (hneq y hy) heq

/-- Equivalent formulation for a continuous gap function, anchored at the left
endpoint. -/
theorem positiveGapPersistsOnIci
    (gap : ℝ → ℝ) (a : ℝ)
    (hgap : ContinuousOn gap (Ici a))
    (hstart : 0 < gap a)
    (hnonzero : ∀ x ∈ Ici a, gap x ≠ 0) :
    ∀ x ∈ Ici a, 0 < gap x := by
  have hzero : ContinuousOn (fun _ : ℝ => 0) (Ici a) := continuousOn_const
  have hneq : ∀ x ∈ Ici a, (0 : ℝ) ≠ gap x := by
    intro x hx
    exact (hnonzero x hx).symm
  exact strictOrderPersistsOnIci (fun _ : ℝ => 0) gap a
    hzero hgap hstart hneq

/-- Gap-function form anchored at an arbitrary point of the ray.  This is the
form useful when positivity is first proved only in an asymptotic regime. -/
theorem positiveGapOnIciFromAnyAnchor
    (gap : ℝ → ℝ) (a b : ℝ)
    (hb : b ∈ Ici a)
    (hgap : ContinuousOn gap (Ici a))
    (hanchor : 0 < gap b)
    (hnonzero : ∀ x ∈ Ici a, gap x ≠ 0) :
    ∀ x ∈ Ici a, 0 < gap x := by
  have hzero : ContinuousOn (fun _ : ℝ => 0) (Ici a) := continuousOn_const
  have hneq : ∀ x ∈ Ici a, (0 : ℝ) ≠ gap x := by
    intro x hx
    exact (hnonzero x hx).symm
  exact strictOrderOnIciFromAnyAnchor (fun _ : ℝ => 0) gap a b
    hb hzero hgap hanchor hneq

/-- A finite certified interval can be attached to a no-crossing ray without
rechecking the sign pointwise beyond the right endpoint. -/
theorem compactCertificateAndNoCrossingRay
    (f g : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b)
    (hcompact : ∀ x ∈ Icc a b, f x < g x)
    (hf : ContinuousOn f (Ici b))
    (hg : ContinuousOn g (Ici b))
    (hneq : ∀ x ∈ Ici b, f x ≠ g x) :
    (∀ x ∈ Icc a b, f x < g x) ∧
      (∀ x ∈ Ici b, f x < g x) := by
  have hbmem : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hstart : f b < g b := hcompact b hbmem
  exact ⟨hcompact,
    strictOrderPersistsOnIci f g b hf hg hstart hneq⟩

end RiemannCvs.ParityOrderContinuation
