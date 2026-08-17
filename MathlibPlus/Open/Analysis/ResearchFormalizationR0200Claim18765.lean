import MathlibPlus.Analysis.Claim50301_18764

namespace MathlibPlus.Open.Analysis.ResearchFormalizationR0200

/-- Claim 18765: specializing the exact weighted-transfer lower bound from
Claim 18764 to σ₀ = 1 + η and σ₁ = 1/2 + ε forces the reciprocal-constant
penalty n^(1/2 + η - ε) at every positive integer atom. -/
def claim18765_criticalLineSquareRootPenalty : Prop :=
  ∀ (η ε C : ℝ) (w : ℕ → ℝ),
    0 < C →
      (∀ n : ℕ, 0 < n →
        (n : ℝ) ^ (-(1 / 2 + ε)) ≤
          C * w n * (n : ℝ) ^ (-(1 + η))) →
        ∀ n : ℕ, 0 < n →
          C⁻¹ * (n : ℝ) ^ (1 / 2 + η - ε) ≤ w n

end MathlibPlus.Open.Analysis.ResearchFormalizationR0200
