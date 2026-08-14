import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

section PlaneFiberFunctions

abbrev TernaryScalar := ZMod 3
abbrev PlaneFunction := TernaryScalar → TernaryScalar → TernaryScalar

/-- The eight nonconstant reduced monomials in the order used by Claim 27742. -/
def planePolynomial (c : Fin 8 → TernaryScalar)
    (i j : TernaryScalar) : TernaryScalar :=
  c 0 * i + c 1 * j + c 2 * i ^ 2 + c 3 * i * j + c 4 * j ^ 2 +
    c 5 * i ^ 2 * j + c 6 * i * j ^ 2 + c 7 * i ^ 2 * j ^ 2

def quadraticPlanePolynomial (c : Fin 5 → TernaryScalar)
    (i j : TernaryScalar) : TernaryScalar :=
  c 0 * i + c 1 * j + c 2 * i ^ 2 + c 3 * i * j + c 4 * j ^ 2

def normalizedPlaneFunctions : Set PlaneFunction :=
  {φ | φ 0 0 = 0}

def quadraticPlaneFunctions : Set PlaneFunction :=
  Set.range (fun c : Fin 5 → TernaryScalar => quadraticPlanePolynomial c)

def higherDegreePlaneFunctions : Set PlaneFunction :=
  normalizedPlaneFunctions \ quadraticPlaneFunctions

/-- Claim 27742: every normalized function has the unique eight-monomial
expression, with the stated quadratic and higher-degree counts. -/
def claim27742 : Prop :=
  (∀ φ : PlaneFunction, φ 0 0 = 0 →
    ∃! c : Fin 8 → TernaryScalar,
      ∀ i j : TernaryScalar, φ i j = planePolynomial c i j) ∧
    Set.ncard normalizedPlaneFunctions = 3 ^ 8 ∧
    Set.ncard normalizedPlaneFunctions = 6561 ∧
    Set.ncard quadraticPlaneFunctions = 3 ^ 5 ∧
    Set.ncard quadraticPlaneFunctions = 243 ∧
    Set.ncard higherDegreePlaneFunctions = 6318

end PlaneFiberFunctions

end MathlibPlus.Open.ResearchFormalization
