import Mathlib
import MathlibPlus.Open.ResearchFormalization.C0079Claim1192

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.C0079Claim1190

open MathlibPlus.Open.ResearchFormalization.C0079Claim1192

noncomputable section

/-- Evaluation in `ℝ` of an integer-coefficient polynomial at the half-shift
variable `b`. -/
def integerPolynomialEvaluation1190 (p : Polynomial ℤ) (b : ℝ) : ℝ :=
  Polynomial.eval₂ (Int.castRingHom ℝ) b p

/-- Coefficientwise membership in `ℤ_{≥0}[b]`. -/
def coefficientwiseNonnegative1190 (p : Polynomial ℤ) : Prop :=
  ∀ k : ℕ, 0 ≤ p.coeff k

/-- The number of available area-at-most-three coordinates in rank `r`. -/
def availableCount1190 (r : ℕ) : ℕ :=
  letI := Classical.propDecidable
  (Finset.univ.filter (fun shape : AreaThreeShape1192 =>
    available1192 shape (r - 1))).card

/-- Claim 1190: every available area-at-most-three gauged flagged-minor
coordinate is represented by an integer polynomial with nonnegative
coefficients after the half-shift, with the exact rank-by-rank availability
counts retained. -/
def claim1190 : Prop :=
  (∀ (r : ℕ), 2 ≤ r →
    let d : ℕ := r - 1
    ∀ (shape : AreaThreeShape1192),
      available1192 shape d →
        ∃ p : Polynomial ℤ,
          (∀ b : ℝ,
            integerPolynomialEvaluation1190 p b =
              alpha1192 shape d (b + 1 / 2)) ∧
          coefficientwiseNonnegative1190 p) ∧
  availableCount1190 2 = 2 ∧
  availableCount1190 3 = 5 ∧
  (∀ r : ℕ, 4 ≤ r → availableCount1190 r = 7)

end

end MathlibPlus.Open.ResearchFormalization.C0079Claim1190
