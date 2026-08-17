import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Algebra

noncomputable section

abbrev Claim50215Polynomial := MvPolynomial ℕ+ ℚ

/-- The weight of a monomial in the component-size variables. -/
def claim50215MonomialWeight (e : ℕ+ →₀ ℕ) : ℕ :=
  e.sum (fun j a => (j : ℕ) * a)

/-- The weight-`n` component of the polynomial ring on `x₁,x₂,…`. -/
def claim50215WeightN (n : ℕ) (p : Claim50215Polynomial) : Prop :=
  ∀ e ∈ p.support, claim50215MonomialWeight e = n

/-- The no-singleton part of the target polynomial sector, with the exceptional
sectors `𝒩₀ = ℚ` and `𝒩₁ = 0` represented in the common carrier. -/
def claim50215PrimitiveSeed (j : ℕ) (p : Claim50215Polynomial) : Prop :=
  if j = 0 then
    ∃ q : ℚ, p = MvPolynomial.C q
  else if j = 1 then
    p = 0
  else
    ∀ e ∈ p.support, e (1 : ℕ+) = 0

/-- The Euler operator on the component-size polynomial carrier. -/
def claim50215EulerOperator (p : Claim50215Polynomial) : Claim50215Polynomial :=
  p.vars.sum (fun j => MvPolynomial.X j * MvPolynomial.pderiv j p)

/-- The index-raising derivation `D₀`. -/
def claim50215D0 (p : Claim50215Polynomial) : Claim50215Polynomial :=
  p.vars.sum (fun j =>
    MvPolynomial.X (j + 1) * MvPolynomial.pderiv j p)

/-- The weighted index-raising derivation `D₁`. -/
def claim50215D1 (p : Claim50215Polynomial) : Claim50215Polynomial :=
  p.vars.sum (fun j =>
    (j : ℚ) • (MvPolynomial.X (j + 1) * MvPolynomial.pderiv j p))

/-- The pendant-defect operator from weight `n-1` to weight `n`; its scalar
coefficient is the algebraic `n - 2`, not natural-number subtraction. -/
def claim50215PendantOperator (n : ℕ) (p : Claim50215Polynomial) :
    Claim50215Polynomial :=
  MvPolynomial.X 1 *
      ((n : ℚ) • claim50215EulerOperator p - (n : ℚ) • p + (2 : ℚ) • p) +
    ((n : ℚ) - 2) • claim50215D1 p +
      (n : ℚ) • claim50215D0 p

/-- Apply the successive operators `B_(j+1),…,B_(j+steps)`. -/
def claim50215RaiseFrom (j steps : ℕ) (p : Claim50215Polynomial) :
    Claim50215Polynomial :=
  match steps with
  | 0 => p
  | s + 1 => claim50215PendantOperator (j + s + 1)
      (claim50215RaiseFrom j s p)

def claim50215TowerExpansion (n : ℕ)
    (q : Fin (n + 1) → Claim50215Polynomial) : Claim50215Polynomial :=
  ∑ j : Fin (n + 1),
    claim50215RaiseFrom j.1 (n - j.1) (q j)

/-- Claim 50215: every weight-`n` component has one and only one expansion
into the primitive seeds and their complete order-`n` towers. -/
def claim50215_primitiveSeedTowers : Prop :=
  ∀ (n : ℕ) (h : Claim50215Polynomial), claim50215WeightN n h →
    ∃! q : Fin (n + 1) → Claim50215Polynomial,
      (∀ j : Fin (n + 1),
        claim50215WeightN j.1 (q j) ∧ claim50215PrimitiveSeed j.1 (q j)) ∧
        h = claim50215TowerExpansion n q

end

end MathlibPlus.Open.Algebra
