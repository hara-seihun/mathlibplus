import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.FormalizationBatch.Graph

/-- Ordinary degree polynomial for a path of positive order. -/
def pathDegreePolynomialValue (h : ℕ) : Polynomial ℕ :=
  if h = 1 then 1 else
    Polynomial.C 2 * Polynomial.X +
      Polynomial.C (h - 2) * Polynomial.X ^ 2

def pathDegreePolynomial : Prop :=
  ∀ h : ℕ, 0 < h →
    (pathDegreePolynomialValue h =
      if h = 1 then 1 else
        Polynomial.C 2 * Polynomial.X +
          Polynomial.C (h - 2) * Polynomial.X ^ 2) ∧
      (h = 1 ∨ 2 ≤ h)

/-- Leg factors and the marked side factors, represented as polynomials in u
with polynomial coefficients in z. -/
def legR (a : ℕ) : Polynomial (Polynomial ℕ) :=
  let u : Polynomial (Polynomial ℕ) := Polynomial.X
  let z : Polynomial (Polynomial ℕ) := Polynomial.C Polynomial.X
  u ^ a + z * (∑ j ∈ Finset.range a, u ^ j)

def legK (a : ℕ) : Polynomial (Polynomial ℕ) :=
  let u : Polynomial (Polynomial ℕ) := Polynomial.X
  ∑ j ∈ Finset.range a,
    u ^ j * Polynomial.C (pathDegreePolynomialValue (a - j))

def sideP (A : Multiset ℕ) : Polynomial (Polynomial ℕ) :=
  (A.map legR).prod

def sideK (A : Multiset ℕ) : Polynomial (Polynomial ℕ) :=
  (A.map (fun a => legK a * (A.erase a |>.map legR).prod)).sum

def legSideFactorsAndMarkedFactors : Prop :=
  (∀ a : ℕ, 0 < a →
    legR a =
        (Polynomial.X : Polynomial (Polynomial ℕ)) ^ a +
          Polynomial.C (Polynomial.X : Polynomial ℕ) *
            (∑ j ∈ Finset.range a,
              (Polynomial.X : Polynomial (Polynomial ℕ)) ^ j) ∧
      legK a =
        ∑ j ∈ Finset.range a,
          (Polynomial.X : Polynomial (Polynomial ℕ)) ^ j *
            Polynomial.C (pathDegreePolynomialValue (a - j))) ∧
    (∀ A : Multiset ℕ,
      sideP A = (A.map legR).prod ∧
        sideK A =
          (A.map (fun a => legK a * (A.erase a |>.map legR).prod)).sum)

/-- Join-irreducibility used in the finite support-semilattice bound. -/
def graphJoinIrreducible [SemilatticeSup α] [OrderBot α] (j : α) : Prop :=
  j ≠ ⊥ ∧ ∀ a b : α, j = a ⊔ b → j = a ∨ j = b

/-- The information bound and its 56-element consequence. -/
def informationBoundOnJoinIrreducibles : Prop :=
  ∀ (α : Type*) [Fintype α] [SemilatticeSup α] [OrderBot α],
    ∀ J : Finset α,
      (∀ j : α, j ∈ J → graphJoinIrreducible j) →
        (∀ j : α, graphJoinIrreducible j → j ∈ J) →
        (∀ x : α,
          ∃ S : Finset α, S ⊆ J ∧ x = S.sup id) →
          Fintype.card α ≤ 2 ^ J.card ∧
            (Fintype.card α = 56 → 6 ≤ J.card)

end MathlibPlus.Open.FormalizationBatch.Graph
