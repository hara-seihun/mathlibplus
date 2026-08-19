import MathlibPlus.Open.ResearchFormalizationBatch_01a00398_0472_7168_885d_1ea758f4c171

namespace MathlibPlus.Analysis

open MathlibPlus.Open

/-- Claim 11643: the exact source logarithmic-kernel carrier obeys the
homogeneous scaling law. -/
def exactScalingLaw_claim11643 : Prop :=
  ∀ (m : ℕ) (σ : ℝ) (c : ℝ) (hc : 0 < c)
    (u v : {x : ℝ // 0 < x}),
    homogeneityB m σ (homogeneityScale c u hc) (homogeneityScale c v hc) =
      Real.rpow c (4 * σ - 4) * homogeneityB m σ u v

end MathlibPlus.Analysis
