import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0879Claim27206

noncomputable section

abbrev R0 := MvPolynomial (Fin 4) ℚ
abbrev EndpointPolynomial := Polynomial R0

def e₁ : R0 := MvPolynomial.X 0
def e₂ : R0 := MvPolynomial.X 1
def e₃ : R0 := MvPolynomial.X 2
def e₄ : R0 := MvPolynomial.X 3

def chi : EndpointPolynomial :=
  Polynomial.X ^ 4 - Polynomial.C e₁ * Polynomial.X ^ 3 +
    Polynomial.C e₂ * Polynomial.X ^ 2 - Polynomial.C e₃ * Polynomial.X +
    Polynomial.C e₄

def cPoly : EndpointPolynomial :=
  Polynomial.X ^ 3 - Polynomial.C e₁ * Polynomial.X ^ 2 +
    Polynomial.C e₂ * Polynomial.X - Polynomial.C e₃

def cModule : Submodule R0 EndpointPolynomial :=
  Submodule.span R0 ({cPoly} : Set EndpointPolynomial)

def chiMultiples : Submodule R0 EndpointPolynomial :=
  LinearMap.range (LinearMap.mulLeft R0 chi)

def endpointModule : Submodule R0 EndpointPolynomial :=
  cModule ⊔ chiMultiples

def lowDegreeModule : Submodule R0 EndpointPolynomial :=
  Submodule.span R0
    ({(1 : EndpointPolynomial), Polynomial.X, Polynomial.X ^ 2} :
      Set EndpointPolynomial)

def lowDegreePolynomial (a : Fin 3 → R0) : EndpointPolynomial :=
  Polynomial.C (a 0) + Polynomial.C (a 1) * Polynomial.X +
    Polynomial.C (a 2) * Polynomial.X ^ 2

def directSumComplement
    (U V : Submodule R0 EndpointPolynomial) : Prop :=
  U ⊔ V = ⊤ ∧ Disjoint U V

def freeComplementCoordinates : Prop :=
  ∀ p : EndpointPolynomial, ∃! q : (Fin 3 → R0) × EndpointPolynomial,
    q.2 ∈ endpointModule ∧ lowDegreePolynomial q.1 + q.2 = p

/-- Claim 27206: the three low powers complement the endpoint module in the
full polynomial ring, with the changed cubic remainder coordinate c(t). -/
def claim27206 : Prop :=
  directSumComplement lowDegreeModule endpointModule ∧
    freeComplementCoordinates

end

end MathlibPlus.Open.ResearchFormalization.R0879Claim27206
