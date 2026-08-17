import MathlibPlus.Open.Analysis.PrimeScoreBatch

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- Claim 1203: the published endpoint has the stated prime count and
score margins, and therefore does not start the strict coefficient bound. -/
def publishedEndpointCounterexample_claim1203 : Prop :=
  let x₀ : ℕ := 42575222481
  let n₀ : ℕ := 1817311115
  let c : ℝ := (1149 : ℝ) / 1000
  let scoreLower : ℝ :=
    (11490003091852194519030898606008869613277 : ℝ) /
      (10 : ℝ) ^ (40 : ℕ)
  let excessLower : ℝ :=
    (97995437480881739846 : ℝ) /
      (10 : ℝ) ^ (20 : ℕ)
  let x : ℝ := x₀
  let scoreExcess : ℝ :=
    (primeCountingReal x : ℝ) - x / D c x
  ¬Nat.Prime x₀ ∧
    primeCountingReal ((x₀ - 1 : ℕ) : ℝ) = n₀ ∧
    primeCountingReal x = n₀ ∧
    scoreLower ≤ B x ∧
    B x < scoreLower + 1 / (10 : ℝ) ^ (40 : ℕ) ∧
    B x > c ∧
    excessLower ≤ scoreExcess ∧
    scoreExcess < excessLower + 1 / (10 : ℝ) ^ (20 : ℕ) ∧
    scoreExcess > 0 ∧
    ¬(∀ y : ℝ, x ≤ y →
      (primeCountingReal y : ℝ) < y / D c y)

end

end MathlibPlus.Open.Analysis
