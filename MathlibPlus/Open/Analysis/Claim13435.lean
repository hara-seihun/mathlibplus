import MathlibPlus.Open.Analysis.RankinBatch_01a008fc

namespace MathlibPlus.Open.Analysis.RankinBatch.Claim13435

/-- The normalized three Rankin jet moments in the positive-weight,
positive-frequency, right-Mellin domain. -/
def normalizedRankinJetMoments : Prop :=
  ∀ (k : ℝ) (n : ℕ) (s : ℂ),
    0 < k →
    1 ≤ n →
    0 < (MathlibPlus.Open.Analysis.RankinBatch.mellinAlpha s k).re →
    MathlibPlus.Open.Analysis.RankinBatch.rankinI₁₀ s k n /
        MathlibPlus.Open.Analysis.RankinBatch.rankinI₀₀ s k n =
      (1 - s) / 2 ∧
    MathlibPlus.Open.Analysis.RankinBatch.rankinI₁₁ s k n /
        MathlibPlus.Open.Analysis.RankinBatch.rankinI₀₀ s k n =
      (s ^ 2 - s + (k : ℂ)) / 4 ∧
    MathlibPlus.Open.Analysis.RankinBatch.rankinI₂₀ s k n /
        MathlibPlus.Open.Analysis.RankinBatch.rankinI₀₀ s k n =
      (s ^ 2 - 3 * s - (k : ℂ) + 2) / 4

end MathlibPlus.Open.Analysis.RankinBatch.Claim13435
