import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_019ffee1_381d_7322_b2f6_d6e3063c8083
import MathlibPlus.Open.ResearchFormalization.R1847Claim32867
import MathlibPlus.Open.ResearchFormalization.R1847Claim32868

namespace MathlibPlus.Open.ResearchFormalization.R1847.Claim32866

noncomputable section

/-- The exact survivor quantity `W_y` from the finite base problem. -/
def survivorQuantity (y : ℕ) : ℝ :=
  (MathlibPlus.Open.ResearchFormalizationBatch_019ffee1_381d_7322_b2f6_d6e3063c8083.baseSurvivorMinimum y : ℝ)

/-- The exact Brun--Titchmarsh tail `T(y,w)`, with the lower endpoint
`v(y) = sqrt (y / log y)` and the upper endpoint `w`. -/
def brunTitchmarshTail (y : ℕ) (w : ℝ) : ℝ :=
  MathlibPlus.Open.ResearchFormalization.R1847.Claim32867.tailSum (y : ℝ) w

/-- The exact Jacobsthal gap carrier at the real cutoff `w`. -/
def jacobsthalGapQuantity (w : ℝ) : ℝ :=
  MathlibPlus.Open.ResearchFormalization.R1847.Claim32868.jacobsthalGap w

/-- Claim 32866: the Brun--Titchmarsh tail extension criterion gives
`J(w) < y` whenever the exact base survivor count exceeds the exact prime
tail. -/
def brunTitchmarshTailExtensionCriterion_claim32866 : Prop :=
  ∀ y : ℕ, 2 ≤ y →
    ∀ w : ℝ,
      survivorQuantity y > brunTitchmarshTail y w →
        jacobsthalGapQuantity w < (y : ℝ)

end

end MathlibPlus.Open.ResearchFormalization.R1847.Claim32866
