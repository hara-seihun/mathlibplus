import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0757Claim24480

noncomputable def oneExteriorP3LowerBound (S p₂ : ℝ) : ℝ :=
  (p₂ ^ 2 - 32 * p₂ + 64 * S) / (S - 4)

noncomputable def totalRootLogConvexityBound (S p₂ : ℝ) : ℝ :=
  p₂ ^ 2 / S

noncomputable def oneExteriorGainSquare (S p₂ : ℝ) : ℝ :=
  4 * (4 * S - p₂) ^ 2 / (S * (S - 4))

noncomputable def claim24480 : Prop :=
  ∀ (S p₂ : ℝ),
    4 < S → 16 < p₂ → p₂ < 4 * S →
      totalRootLogConvexityBound S p₂ <
          oneExteriorP3LowerBound S p₂ ∧
        oneExteriorP3LowerBound S p₂ - totalRootLogConvexityBound S p₂ =
          oneExteriorGainSquare S p₂ ∧
        0 ≤ oneExteriorGainSquare S p₂

end MathlibPlus.Open.ResearchFormalization.R0757Claim24480
