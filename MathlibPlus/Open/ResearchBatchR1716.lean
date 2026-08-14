import Mathlib

noncomputable section
open MvPolynomial

namespace MathlibPlus.Open.ResearchBatchR1716

abbrev ComponentVariable := {j : ℕ // 0 < j}
abbrev ComponentProfilePolynomial := MvPolynomial ComponentVariable ℤ

def componentDegree (d : ComponentVariable →₀ ℕ) : ℕ :=
  d.support.sum (fun i => d i)

def eulerOperator (p : ComponentProfilePolynomial) : ComponentProfilePolynomial :=
  (vars p).sum (fun j => X j * pderiv j p)

def hasZeroComponentDegreeOne (p : ComponentProfilePolynomial) : Prop :=
  ∀ d, componentDegree d = 1 → coeff d p = 0

def eulerMinusOneInjectiveAboveComponentDegreeOne : Prop :=
  (∀ ⦃p q : ComponentProfilePolynomial⦄,
      hasZeroComponentDegreeOne p →
      hasZeroComponentDegreeOne q →
      eulerOperator p - p = eulerOperator q - q → p = q) ∧
    (∀ (d : ComponentVariable →₀ ℕ) (a : ℤ),
      eulerOperator (monomial d a) = monomial d ((componentDegree d : ℤ) * a)) ∧
    (∀ (d : ComponentVariable →₀ ℕ) (a : ℤ),
      eulerOperator (monomial d a) - monomial d a =
        monomial d (((componentDegree d : ℤ) - 1) * a)) ∧
    (∀ q : ℕ, 2 ≤ q → (q : ℤ) - 1 ≠ 0)

def x₁ : MvPolynomial (Fin 3) ℤ := X 0
def x₂ : MvPolynomial (Fin 3) ℤ := X 1
def x₃ : MvPolynomial (Fin 3) ℤ := X 2

def cubicRow (A B C : ℕ) : MvPolynomial (Fin 3) ℤ :=
  (A : ℤ) • x₁ ^ 3 + (B : ℤ) • (x₁ * x₂) + (C : ℤ) • x₃

def cubicMarkedRow (A B C : ℕ) : MvPolynomial (Fin 3) ℤ :=
  pderiv 0 (cubicRow A B C)

def markedCubicRowDerivativeFormula : Prop :=
  (∀ A B C : ℕ,
      cubicMarkedRow A B C =
        (3 * (A : ℤ)) • x₁ ^ 2 + (B : ℤ) • x₂) ∧
    (∀ A A' B B' C C' : ℕ,
      cubicMarkedRow A B C = cubicMarkedRow A' B' C' →
        A = A' ∧ B = B') ∧
    (∀ L L' : ℕ,
      pderiv 0 ((L : ℤ) • x₁) = pderiv 0 ((L' : ℤ) • x₁) → L = L')

end MathlibPlus.Open.ResearchBatchR1716
