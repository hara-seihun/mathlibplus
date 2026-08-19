import MathlibPlus.Open.ResearchFormalization.C0079Claim1192

namespace MathlibPlus.Open.ResearchFormalization.C0077Claim1161

noncomputable section

open Polynomial
open MathlibPlus.Open.ResearchFormalization.C0079Claim1192

/-- Claim 1161 with the exact C-0077 cup coordinates.  The quotient formulas
are guarded at poles, while the cross-multiplied identities are unconditional;
polynomiality is recorded as divisibility in `Polynomial ℝ`. -/
def explicitAllRankCupCoordinateFormulas_claim1161 : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    (∀ a : ℝ,
      let b : ℝ := a - 1 / 2
      let X : ℝ := 2 * b + d + 1
      alphaEmpty1192 d a = principalProduct1192 d b ∧
        X * alphaOne1192 d a = 2 * b * principalProduct1192 d b ∧
        (X ≠ 0 →
          alphaOne1192 d a = (2 * b / X) * principalProduct1192 d b) ∧
        (2 ≤ d →
          2 * X * (X + 1) * alphaTwo1192 d a =
              (8 * b ^ 2 + 4 * ((d : ℝ) + 2) * b +
                ((d - 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ)) *
                principalProduct1192 d b ∧
            2 * X * (X - 1) * alphaOneOne1192 d a =
              (8 * b ^ 2 + 4 * (d : ℝ) * b +
                ((d + 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ)) *
                principalProduct1192 d b ∧
            (X ≠ 0 → X + 1 ≠ 0 →
              alphaTwo1192 d a =
                (8 * b ^ 2 + 4 * ((d : ℝ) + 2) * b +
                  ((d - 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ)) /
                  (2 * X * (X + 1)) * principalProduct1192 d b) ∧
            (X ≠ 0 → X - 1 ≠ 0 →
              alphaOneOne1192 d a =
                (8 * b ^ 2 + 4 * (d : ℝ) * b +
                  ((d + 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ)) /
                  (2 * X * (X - 1)) * principalProduct1192 d b))) ∧
      (∃ P : Polynomial ℝ, ∃ q₁ : Polynomial ℝ,
        P = (Polynomial.C (d.factorial : ℝ) *
          ∏ p ∈ Finset.range (d + 1),
            ∏ q ∈ Finset.range (d + 1),
              (if p < q then
                Polynomial.C 2 * Polynomial.X +
                  Polynomial.C ((p + q + 1 : ℕ) : ℝ)
              else 1)) ∧
        (∀ b : ℝ, Polynomial.eval b P = principalProduct1192 d b) ∧
        (Polynomial.C 2 * Polynomial.X + Polynomial.C ((d : ℝ) + 1)) * q₁ =
          Polynomial.C 2 * Polynomial.X * P ∧
        (2 ≤ d →
          ∃ q₂ q₁₁ : Polynomial ℝ,
            (2 * (Polynomial.C 2 * Polynomial.X +
              Polynomial.C ((d : ℝ) + 1)) *
              ((Polynomial.C 2 * Polynomial.X +
                Polynomial.C ((d : ℝ) + 1)) + 1)) * q₂ =
              (Polynomial.C 8 * Polynomial.X ^ 2 +
                Polynomial.C (4 * ((d : ℝ) + 2)) * Polynomial.X +
                Polynomial.C (((d - 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ))) * P ∧
            (2 * (Polynomial.C 2 * Polynomial.X +
              Polynomial.C ((d : ℝ) + 1)) *
              ((Polynomial.C 2 * Polynomial.X +
                Polynomial.C ((d : ℝ) + 1)) - 1)) * q₁₁ =
              (Polynomial.C 8 * Polynomial.X ^ 2 +
                Polynomial.C (4 * (d : ℝ)) * Polynomial.X +
                Polynomial.C (((d + 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ))) * P))

end

end MathlibPlus.Open.ResearchFormalization.C0077Claim1161
