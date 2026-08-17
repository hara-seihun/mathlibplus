import MathlibPlus.Open.Analysis.PrimeScoreBatch

namespace MathlibPlus.Open.Analysis

noncomputable section

/--
Claim 1207: the exact prime-free plateau, its constant prime count, and the
unique 1.149 crossing, with the displayed decimal retained as a prefix
interval.
-/
def primeCountingUniquePlateauCrossing_claim1207 : Prop :=
  let x₀ : ℝ := 42575222481
  let p₁ : ℝ := 42575222531
  let n₀ : ℕ := 1817311115
  let crossingLower : ℝ :=
    (425752225049836706141810389440712642818 : ℝ) /
      (10 : ℝ) ^ (28 : ℕ)
  let crossingUpper : ℝ :=
    (425752225049836706141810389440712642819 : ℝ) /
      (10 : ℝ) ^ (28 : ℕ)
  ¬Nat.Prime 42575222481 ∧
    primeCountingReal x₀ = n₀ ∧
    Nat.Prime 42575222531 ∧
    primeCountingReal p₁ = 1817311116 ∧
    (∀ p : ℕ,
      42575222481 < p → p < 42575222531 → ¬Nat.Prime p) ∧
    (∀ x : ℝ, x ∈ Set.Ico x₀ p₁ → primeCountingReal x = n₀) ∧
    (∃! r : ℝ,
      r ∈ Set.Ioo x₀ p₁ ∧ B r = (1149 : ℝ) / 1000) ∧
    (∀ r : ℝ,
      r ∈ Set.Ioo x₀ p₁ → B r = (1149 : ℝ) / 1000 →
        crossingLower ≤ r ∧ r < crossingUpper)

end

end MathlibPlus.Open.Analysis
