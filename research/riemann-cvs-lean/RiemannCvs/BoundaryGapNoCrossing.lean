import RiemannCvs.SylvesterNoCrossing

/-!
# Boundary gaps as a no-crossing certificate

For a rank-one Sylvester relation

`J Q₊ - Q₋ J = β ⊗ η`,

a common eigenvalue forces the product of two boundary overlaps to vanish.
This file isolates a useful way to prove that those overlaps are nonzero.

If an eigenvector has eigenvalue `lambda`, while every vector in the kernel of
the relevant boundary functional has Rayleigh value at least `mu > lambda`,
then the eigenvector cannot lie in that boundary kernel.  Applying this in both
parity sectors turns two strict constrained-ground gaps into a no-crossing
certificate.

No concrete CvS spectral estimate is asserted here.  The strict constrained
bounds and the energy identities remain explicit hypotheses.
-/

namespace RiemannCvs.BoundaryGapNoCrossing

/-- A strict gap below the boundary-constrained energy forces the corresponding
boundary value of an eigenvector to be nonzero.

The functions `energy` and `normSq` are deliberately abstract.  In a Hilbert
space application they are the quadratic form and squared norm. -/
theorem boundaryValueNonzeroOfStrictConstraintGap
    {E : Type*}
    (boundary : E →ₗ[ℝ] ℝ)
    (energy normSq : E → ℝ)
    (x : E) (lambda mu : ℝ)
    (hnorm : 0 < normSq x)
    (heigenEnergy : energy x = lambda * normSq x)
    (hconstraint :
      ∀ z, boundary z = 0 → mu * normSq z ≤ energy z)
    (hgap : lambda < mu) :
    boundary x ≠ 0 := by
  intro hboundary
  have hbound := hconstraint x hboundary
  rw [heigenEnergy] at hbound
  nlinarith

section Sylvester

variable {E O : Type*}
variable [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup O] [Module ℝ O]

/-- Two strict boundary-constrained gaps rule out a common eigenvalue across a
rank-one Sylvester relation.

In a self-adjoint application, `phi` is pairing with an odd eigenvector `y`,
and `hphiBoundary` identifies `phi beta` with its odd boundary overlap. -/
theorem noCommonEigenvalueFromConstraintGaps
    (Qplus : E →ₗ[ℝ] E)
    (Qminus : O →ₗ[ℝ] O)
    (J : E →ₗ[ℝ] O)
    (eta : E →ₗ[ℝ] ℝ)
    (phi : O →ₗ[ℝ] ℝ)
    (beta : O)
    (oddBoundary : O →ₗ[ℝ] ℝ)
    (evenEnergy evenNormSq : E → ℝ)
    (oddEnergy oddNormSq : O → ℝ)
    (x : E) (y : O)
    (lambda muPlus muMinus : ℝ)
    (hSylvester :
      ∀ z, J (Qplus z) - Qminus (J z) = eta z • beta)
    (hx : Qplus x = lambda • x)
    (hphi : ∀ z, phi (Qminus z) = lambda * phi z)
    (hxNorm : 0 < evenNormSq x)
    (hyNorm : 0 < oddNormSq y)
    (hxEnergy : evenEnergy x = lambda * evenNormSq x)
    (hyEnergy : oddEnergy y = lambda * oddNormSq y)
    (hEvenConstraint :
      ∀ z, eta z = 0 → muPlus * evenNormSq z ≤ evenEnergy z)
    (hOddConstraint :
      ∀ z, oddBoundary z = 0 → muMinus * oddNormSq z ≤ oddEnergy z)
    (hPlusGap : lambda < muPlus)
    (hMinusGap : lambda < muMinus)
    (hphiBoundary : phi beta = oddBoundary y) :
    False := by
  have hetaNonzero : eta x ≠ 0 :=
    boundaryValueNonzeroOfStrictConstraintGap
      eta evenEnergy evenNormSq x lambda muPlus
      hxNorm hxEnergy hEvenConstraint hPlusGap
  have hOddBoundaryNonzero : oddBoundary y ≠ 0 :=
    boundaryValueNonzeroOfStrictConstraintGap
      oddBoundary oddEnergy oddNormSq y lambda muMinus
      hyNorm hyEnergy hOddConstraint hMinusGap
  have hphiBetaNonzero : phi beta ≠ 0 := by
    rw [hphiBoundary]
    exact hOddBoundaryNonzero
  exact RiemannCvs.SylvesterNoCrossing.noCommonEigenvalueWhenBoundaryOverlapsNonzero
    Qplus Qminus J eta phi beta x lambda
    hSylvester hx hphi hetaNonzero hphiBetaNonzero

end Sylvester

end RiemannCvs.BoundaryGapNoCrossing
