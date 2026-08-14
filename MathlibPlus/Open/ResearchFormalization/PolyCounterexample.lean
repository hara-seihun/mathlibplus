import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

abbrev PolyVars := Fin 5
abbrev Poly := MvPolynomial PolyVars ℚ

def polyVar (i : PolyVars) : Poly := MvPolynomial.X i

def t : Poly := polyVar 0
def z : Poly := polyVar 1
def x₂ : Poly := polyVar 2
def x₃ : Poly := polyVar 3
def x₄ : Poly := polyVar 4

def H : Poly := t ^ 4 + z * t ^ 3 + z ^ 4 + x₄
def w₁ : Poly := z * x₃
def w₂ : Poly := z ^ 2 * x₂

def F₀ : Poly := H
def F₁₂ : Poly := H + w₁ + w₂
def F₁ : Poly := H + w₁
def F₂ : Poly := H + w₂

def polyWeight (i : PolyVars) : ℕ :=
  if i.val = 0 then 1 else if i.val = 1 then 1 else
    if i.val = 2 then 2 else if i.val = 3 then 3 else 4

def coefficientwiseNonnegative (p : Poly) : Prop :=
  ∀ m, 0 ≤ MvPolynomial.coeff m p

def linearMonicInX₄ (p : Poly) : Prop :=
  (∀ m ∈ p.support, m 4 ≤ 1) ∧
  MvPolynomial.coeff (Finsupp.single 4 1) p = 1

def hasUniversalTopTerms (p : Poly) : Prop :=
  MvPolynomial.coeff (Finsupp.single 0 4) p = 1 ∧
  MvPolynomial.coeff (Finsupp.single 1 1 + Finsupp.single 0 3) p = 1 ∧
  MvPolynomial.coeff (Finsupp.single 1 4) p = 1 ∧
  MvPolynomial.coeff (Finsupp.single 4 1) p = 1

def ambientProperties (p : Poly) : Prop :=
  coefficientwiseNonnegative p ∧
  MvPolynomial.IsWeightedHomogeneous polyWeight p 4 ∧
  linearMonicInX₄ p ∧
  hasUniversalTopTerms p

def sameTDerivative (p q : Poly) : Prop :=
  MvPolynomial.pderiv 0 p = MvPolynomial.pderiv 0 q

/-- Exact explicit polynomial counterexample from admitted claim 47264. -/
def claim47264 : Prop :=
  ambientProperties F₀ ∧
  ambientProperties F₁₂ ∧
  ambientProperties F₁ ∧
  ambientProperties F₂ ∧
  sameTDerivative (F₀ * F₁₂) (F₁ * F₂) ∧
  F₀ * F₁₂ - F₁ * F₂ = -(z ^ 3 * x₂ * x₃) ∧
  z ^ 3 * x₂ * x₃ ≠ 0 ∧
  F₀ * F₁₂ ≠ F₁ * F₂

end

end MathlibPlus.Open.ResearchFormalization
