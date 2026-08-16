import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.O0356

/-- Claim 15668: the exact Record 33 radius identities and the hypotheses
`0 ≤ R_j ≤ 1` force the resummed pair rate to be nonpositive. -/
def claim15668_RHRadiusBoundsForceNonpositivePairRate : Prop :=
  ∀ (r₁ r₂ n₁ n₂ R₁ R₂ : ℝ),
    2 * r₁ + n₁ ^ 2 = R₁ ^ 2 - 1 →
      2 * r₂ + n₂ ^ 2 = R₂ ^ 2 - 1 →
        0 ≤ R₁ →
          R₁ ≤ 1 →
            0 ≤ R₂ →
              R₂ ≤ 1 →
                r₁ + r₂ + n₁ * n₂ ≤ 0

end MathlibPlus.Open.ResearchFormalization.O0356
