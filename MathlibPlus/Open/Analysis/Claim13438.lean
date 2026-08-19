import MathlibPlus.Open.Analysis.RankinBatch_01a008fc
import MathlibPlus.Open.Analysis.Claim13435
import MathlibPlus.Analysis.Claim13437

namespace MathlibPlus.Open.Analysis.Claim13438

noncomputable section

open MathlibPlus.Open.Analysis.RankinBatch

/-- Claim 13438: the first-jet Gram and geodesic Hessian have equal and
opposite normalized Schur reserves over the zeroth Rankin jet. -/
def claim13438 : Prop :=
  ∀ (k : ℝ) (n : ℕ) (s : ℂ),
    0 < k →
      1 ≤ n →
        0 < (mellinAlpha s k).re →
          let α : ℂ := mellinAlpha s k
          let I₀₀ : ℂ := rankinI₀₀ s k n
          let I₁₀ : ℂ := rankinI₁₀ s k n
          let I₁₁ : ℂ := rankinI₁₁ s k n
          let I₂₀ : ℂ := rankinI₂₀ s k n
          I₀₀ ≠ 0 ∧
            Matrix.det
                (MathlibPlus.Analysis.firstJetGram_claim13437
                  I₁₁ I₁₀ I₀₀) / I₀₀ ^ 2 = α / 4 ∧
            Matrix.det
                (MathlibPlus.Analysis.geodesicHessian_claim13437
                  I₂₀ I₁₀ I₀₀) / I₀₀ ^ 2 = -(α / 4) ∧
            I₁₁ - I₁₀ ^ 2 / I₀₀ = (α / 4) * I₀₀ ∧
            I₂₀ - I₁₀ ^ 2 / I₀₀ = -(α / 4) * I₀₀

end

end MathlibPlus.Open.Analysis.Claim13438
