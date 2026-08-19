import Mathlib

open scoped BigOperators
open Polynomial

namespace MathlibPlus.Open.ResearchFormalization.R1351Claim41267

noncomputable section

/-- The five candidate `(a,c)` pairs left by the exact arithmetic reduction. -/
def candidateRows : Fin 5 → ℕ × ℕ :=
  ![(3, 2), (6, 2), (6, 3), (12, 4), (30, 5)]

/-- The primitive integer quadratics obtained after the displayed
`d-b` substitution in the five candidate rows. -/
def candidateQuadratic : Fin 5 → Polynomial ℤ :=
  ![(Polynomial.X : Polynomial ℤ) ^ 2 - 3 * Polynomial.X - 1,
    7 * (Polynomial.X : Polynomial ℤ) ^ 2 - 13 * Polynomial.X - 15,
    (Polynomial.X : Polynomial ℤ) ^ 2 - 3 * Polynomial.X - 3,
    5 * (Polynomial.X : Polynomial ℤ) ^ 2 - 14 * Polynomial.X - 36,
    85 * (Polynomial.X : Polynomial ℤ) ^ 2 - 189 * Polynomial.X - 1300]

/-- The exact discriminants of those five quadratics. -/
def candidateDiscriminant : Fin 5 → ℤ :=
  ![13, 589, 21, 916, 477721]

/-- The rational differences `d-b` in the candidate order. -/
def candidateDelta : Fin 5 → ℚ :=
  ![2, 6, 4, 9, 26]

/-- The coefficient discriminant of an integer quadratic. -/
def quadraticDiscriminant (Q : Polynomial ℤ) : ℤ :=
  Q.coeff 1 ^ 2 - 4 * Q.coeff 2 * Q.coeff 0

/-- The exact substitution formula for the rational difference. -/
def substitutionDelta (a c : ℕ) : ℚ :=
  ((a - c : ℕ) : ℚ) * (a * c + 6) / (a * c)

/-- The two identities and the lower bounds from item 2. -/
def leafComparisonSetup (a b c d : ℕ) : Prop :=
  2 ≤ a ∧ 2 ≤ b ∧ 2 ≤ c ∧ 2 ≤ d ∧
    a * (a - 1) * b * (b - 1) = c * (c - 1) * d * (d - 1) ∧
    (a : ℚ) + b - 6 / a = (c : ℚ) + d - 6 / c

/-- Each displayed quadratic has the stated discriminant, a nonsquare
integer discriminant, and no integer root. -/
def candidateQuadraticObstruction : Prop :=
  ∀ k : Fin 5,
    quadraticDiscriminant (candidateQuadratic k) = candidateDiscriminant k ∧
      (¬ ∃ z : ℤ, z ^ 2 = candidateDiscriminant k) ∧
      (¬ ∃ z : ℤ,
        Polynomial.eval z (candidateQuadratic k) = 0)

/-- Claim 41267: the exact candidate reduction and substitution produce the
five displayed quadratics, whose nonsquare discriminants exclude every
integer `b,d ≥ 2`. -/
def claim_41267 : Prop :=
  candidateQuadraticObstruction ∧
    ∀ (a b c d : ℕ),
      leafComparisonSetup a b c d →
        a > c →
          ∃ k : Fin 5,
            (a, c) = candidateRows k ∧
              (d : ℚ) - b = substitutionDelta a c ∧
              (d : ℚ) - b = candidateDelta k ∧
              Polynomial.eval (b : ℤ) (candidateQuadratic k) = 0 ∧
              ¬ ∃ z : ℤ,
                Polynomial.eval z (candidateQuadratic k) = 0

end

end MathlibPlus.Open.ResearchFormalization.R1351Claim41267
