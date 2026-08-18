import Mathlib
import MathlibPlus.Algebra.Claim27203

namespace MathlibPlus.Open.ResearchFormalization.R0879Claim27205

noncomputable section

abbrev R0 := MvPolynomial (Fin 4) ℚ
abbrev EndpointPolynomial := Polynomial R0
abbrev RootRing := MvPolynomial (Fin 4) ℚ

def e₁ : R0 := MvPolynomial.X 0
def e₂ : R0 := MvPolynomial.X 1
def e₃ : R0 := MvPolynomial.X 2
def e₄ : R0 := MvPolynomial.X 3

def rootValue : Fin 4 → RootRing :=
  ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3]

def rootElementary : Fin 4 → RootRing :=
  ![rootValue 0 + rootValue 1 + rootValue 2 + rootValue 3,
    rootValue 0 * rootValue 1 + rootValue 0 * rootValue 2 +
      rootValue 0 * rootValue 3 + rootValue 1 * rootValue 2 +
      rootValue 1 * rootValue 3 + rootValue 2 * rootValue 3,
    rootValue 0 * rootValue 1 * rootValue 2 + rootValue 0 * rootValue 1 *
        rootValue 3 + rootValue 0 * rootValue 2 * rootValue 3 +
      rootValue 1 * rootValue 2 * rootValue 3,
    rootValue 0 * rootValue 1 * rootValue 2 * rootValue 3]

def rootCoefficientMap : R0 →+* RootRing :=
  MvPolynomial.eval₂Hom (algebraMap ℚ RootRing) rootElementary

def chi : EndpointPolynomial :=
  Polynomial.X ^ 4 - Polynomial.C e₁ * Polynomial.X ^ 3 +
    Polynomial.C e₂ * Polynomial.X ^ 2 - Polynomial.C e₃ * Polynomial.X +
    Polynomial.C e₄

def cPoly : EndpointPolynomial :=
  Polynomial.X ^ 3 - Polynomial.C e₁ * Polynomial.X ^ 2 +
    Polynomial.C e₂ * Polynomial.X - Polynomial.C e₃

def fourRootConstancy (J : EndpointPolynomial) : Prop :=
  ∀ i j : Fin 4,
    Polynomial.eval₂ rootCoefficientMap (rootValue i) (Polynomial.X * J) =
      Polynomial.eval₂ rootCoefficientMap (rootValue j) (Polynomial.X * J)

def fourRootDivision (J : EndpointPolynomial) : Prop :=
  ∃ k : R0, ∃ L : EndpointPolynomial,
    Polynomial.X * J = Polynomial.C k + chi * L

def cModule : Submodule R0 EndpointPolynomial :=
  Submodule.span R0 ({cPoly} : Set EndpointPolynomial)

def chiMultiples : Submodule R0 EndpointPolynomial :=
  LinearMap.range (LinearMap.mulLeft R0 chi)

def endpointModule : Submodule R0 EndpointPolynomial :=
  cModule ⊔ chiMultiples

def endpointModuleMembership (J : EndpointPolynomial) : Prop :=
  J ∈ endpointModule

def endpointModuleRepresentation (J : EndpointPolynomial) : Prop :=
  ∃ a : R0, ∃ L : EndpointPolynomial,
    J = Polynomial.C a * cPoly + chi * L

def internalDirectSumWithin
    (U V W : Submodule R0 EndpointPolynomial) : Prop :=
  U ⊔ V = W ∧ Disjoint U V

/-- Claim 27205: four-root constancy is equivalent to the quartic division
form, and cancellation identifies the endpoint module with the scalar c(t)
and full chi(t)-multiple summands. -/
def claim27205 : Prop :=
  (∀ J : EndpointPolynomial, fourRootConstancy J ↔ fourRootDivision J) ∧
    (∀ J : EndpointPolynomial,
      fourRootDivision J ↔ endpointModuleRepresentation J) ∧
    (∀ J : EndpointPolynomial,
      endpointModuleMembership J ↔ endpointModuleRepresentation J) ∧
    internalDirectSumWithin cModule chiMultiples endpointModule

end

end MathlibPlus.Open.ResearchFormalization.R0879Claim27205
