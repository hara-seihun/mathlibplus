import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1266Claim30804

noncomputable section

open scoped BigOperators

abbrev QPoly := Polynomial ℚ
abbrev QFunc := FractionRing QPoly

def dsJ (d : Nat) : QPoly :=
  (1 + Polynomial.X) ^ d - Polynomial.X ^ d -
    Polynomial.C (d : ℚ) * Polynomial.X ^ (d - 1)

def dsC0 (a b : Nat) : QPoly :=
  (1 + Polynomial.X) ^ (a + b) +
    (1 + Polynomial.X) ^ a * Polynomial.X ^ (b + 1) +
    Polynomial.X ^ (a + b + 2)

def dsC1 (a b : Nat) : QPoly :=
  dsJ b * ((1 + Polynomial.X) ^ a + Polynomial.X ^ (a + 1)) +
    (1 + Polynomial.X) ^ (a + b) +
    (1 + Polynomial.X) ^ a * Polynomial.X ^ (b + 1) -
    Polynomial.X ^ (a + b + 1) -
    Polynomial.C (a + 1 : ℚ) * Polynomial.X ^ (a + b)

def dsDelta (a b : Nat) : QPoly :=
  dsC1 a b ^ 2 - 4 * dsC0 a b * dsJ a * dsJ b

def dsE (a b : Nat) : QPoly :=
  (1 + Polynomial.X) ^ a * Polynomial.X ^ (b - 1) *
    (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (b : ℚ))

def dsOrderAtZero (p : QPoly) (n : Nat) : Prop :=
  (∀ k < n, p.coeff k = 0) ∧ p.coeff n ≠ 0

def dsSquareInQFunc (p : QPoly) : Prop :=
  ∃ q : QFunc, q ^ 2 = algebraMap QPoly QFunc p

def intPolynomialToQ (q : Polynomial ℤ) : QPoly :=
  q.map (Int.castRingHom ℚ)

def integralDiscriminantSquareRoot (a b : Nat) (q : Polynomial ℤ) : Prop :=
  intPolynomialToQ q ^ 2 = dsDelta a b

def displayedRootNextCoefficient (a b c : Nat) (q : Polynomial ℤ) : Prop :=
  ∃ s : ℤ,
    (s = 1 ∨ s = -1) ∧
      (q.coeff ((a - 1) / 2) : ℚ) = (s : ℚ) * (2 * c) ∧
        (q.coeff ((a + 1) / 2) : ℚ) =
          (s : ℚ) * ((c : ℚ) ^ 3 + 2 * (b : ℚ) * c + 1 / (c : ℚ))

def rootCoefficientObstruction (a b c : Nat) : Prop :=
  (∀ q : Polynomial ℤ,
    integralDiscriminantSquareRoot a b q →
      displayedRootNextCoefficient a b c q) ∧
    ¬ ∃ r : ℤ,
      (r : ℚ) =
        (c : ℚ) ^ 3 + 2 * (b : ℚ) * c + 1 / (c : ℚ)

/-- Claim 30804: the strict-range valuation and coefficient obstruction,
including the integral-root implication for the displayed next coefficient. -/
def claim_30804 : Prop :=
  ∀ a b : Nat, 2 ≤ a → 2 ≤ b → a < 2 * b - 1 →
    dsOrderAtZero (dsDelta a b) (a - 1) ∧
      (dsDelta a b).coeff (a - 1) = 4 * (a : ℚ) ∧
        (Even a → Odd (a - 1)) ∧
          ((Odd a ∧ ¬ ∃ c : Nat, c ^ 2 = a) →
            ¬ ∃ q : ℚ, q ^ 2 = 4 * (a : ℚ)) ∧
            (∀ c : Nat, a = c ^ 2 → Odd a → c > 1 →
              rootCoefficientObstruction a b c) ∧
              ¬ dsSquareInQFunc (dsDelta a b)

end

end MathlibPlus.Open.ResearchFormalization.R1266Claim30804
