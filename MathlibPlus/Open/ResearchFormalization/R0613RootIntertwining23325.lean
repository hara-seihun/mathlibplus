import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0613RootIntertwining

noncomputable section

abbrev PositiveIndex := ℕ+
abbrev CoefficientRing := MvPolynomial PositiveIndex ℚ
abbrev RootRing := Polynomial CoefficientRing
abbrev ToricRing := MvPolynomial (Fin 2) ℚ

private def rootZ : RootRing := Polynomial.X

private def rootX (k : PositiveIndex) : RootRing :=
  Polynomial.C (MvPolynomial.X k)

/-- The scalar root-closure operator, with the coefficient index `k`
representing the variable `x_(k+1)`. -/
private def rootOperator (P : RootRing) : RootRing :=
  rootZ * P +
    P.support.sum (fun k =>
      Polynomial.C (MvPolynomial.X (Nat.succPNat k) * P.coeff k))

private def toricU : ToricRing := MvPolynomial.X 0

private def toricV : ToricRing := MvPolynomial.X 1

private def toricCoefficientMap : CoefficientRing →+* ToricRing :=
  MvPolynomial.eval₂Hom (algebraMap ℚ ToricRing)
    (fun k => toricU * toricV ^ (k : ℕ))

private def toricSpecialization : RootRing →ₐ[ℚ] ToricRing :=
  RingHom.toRatAlgHom (Polynomial.eval₂RingHom toricCoefficientMap toricV)

private def scalarS : RootRing := rootZ + rootX 1

private def scalarW : ToricRing := toricV * (1 + toricU)

/-- Claim 23325: the root operator intertwines with the universal singleton
under the exact toric specialization, and the singleton maps to `w`. -/
def claim23325 : Prop :=
  (∀ P : RootRing,
    toricSpecialization (rootOperator P) =
      scalarW * toricSpecialization P) ∧
    toricSpecialization scalarS = scalarW

end

end MathlibPlus.Open.ResearchFormalization.R0613RootIntertwining
