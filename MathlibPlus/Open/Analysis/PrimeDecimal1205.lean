import MathlibPlus.Open.Analysis.PrimeScoreBatch

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- Claim 1205: the strict bound with the repaired decimal coefficient holds
from the published endpoint, while the preceding integer does not. -/
def strictDecimalCoefficientRepair_claim1205 : Prop :=
  let x₀ : ℕ := 42575222481
  let c : ℝ := (114900031 : ℝ) / 100000000
  let aStar : ℝ := B (x₀ : ℝ)
  let marginLower : ℝ :=
    (81478054809691 : ℝ) /
      (10 : ℝ) ^ (23 : ℕ)
  let priorMarginLower : ℝ :=
    (12076708 : ℝ) /
      (10 : ℝ) ^ (15 : ℕ)
  let validStart : ℕ → Prop := fun n =>
    ∀ x : ℝ, (n : ℝ) ≤ x →
      (primeCountingReal x : ℝ) < x / D c x
  let priorMargin : ℝ := B ((x₀ - 1 : ℕ) : ℝ) - c
  (marginLower ≤ c - aStar ∧
      c - aStar < marginLower + 1 / (10 : ℝ) ^ (23 : ℕ) ∧
      0 < c - aStar) ∧
    (∀ x : ℝ, (x₀ : ℝ) ≤ x →
      (primeCountingReal x : ℝ) < x / D c x) ∧
    priorMarginLower ≤ priorMargin ∧
    priorMargin < priorMarginLower + 1 / (10 : ℝ) ^ (15 : ℕ) ∧
    ¬validStart (x₀ - 1) ∧
    IsLeast {n : ℕ | validStart n} x₀

end

end MathlibPlus.Open.Analysis
