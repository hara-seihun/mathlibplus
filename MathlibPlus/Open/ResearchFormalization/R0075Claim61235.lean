import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0075Claim61235

noncomputable section

/-- The exact causal-cone threshold in Claim 61235. -/
def birthFactorThreshold (n : ℕ) : ℝ :=
  2 * Real.sqrt ((2 * (n : ℝ) - 1) * (2 * (n : ℝ)))

/-- The complete birth factor, including its power prefactor. -/
def fullBirthFactor (n : ℕ) (y : ℝ) : ℝ :=
  (y ^ (2 * n - 2) / (Nat.factorial (2 * n - 2) : ℝ)) *
    (1 - y ^ 2 /
      (4 * (2 * (n : ℝ) - 1) * (2 * (n : ℝ))))

/-- Claim 61235: the full factor has the corrected three-way sign
trichotomy, including the extra zero at `y = 0` for every `n ≥ 2`. -/
def claim61235_correctedFullBirthFactorSign : Prop :=
  (∀ n : ℕ, 1 ≤ n →
    ∀ y : ℝ, 0 ≤ y →
      (fullBirthFactor n y > 0 ↔
        y < birthFactorThreshold n ∧ (n = 1 ∨ y > 0)) ∧
      (fullBirthFactor n y = 0 ↔
        y = birthFactorThreshold n ∨ (2 ≤ n ∧ y = 0)) ∧
      (fullBirthFactor n y < 0 ↔
        y > birthFactorThreshold n)) ∧
  fullBirthFactor 1 0 > 0 ∧
  (∀ n : ℕ, 2 ≤ n → fullBirthFactor n 0 = 0)

end
end MathlibPlus.Open.ResearchFormalization.R0075Claim61235
