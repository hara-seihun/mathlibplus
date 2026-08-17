import Mathlib
import MathlibPlus.Open.ResearchFormalization.SingleEffectiveFacePhaseFlux15411

open Filter

namespace MathlibPlus.Open.ResearchFormalization.ShrinkingActionGapRequiresScaledMargin15412

/-- Claim 15412: when the action gap itself tends to zero, the class of
errors negligible on the ambient L-scale is strictly larger than the class
negligible on the exact phase-speed margin L times the action gap. -/
def shrinkingActionGapRequiresScaledMargin_claim15412 : Prop :=
  ∀ (delta : ℕ → ℝ),
    (∀ L : ℕ, 0 < delta L) →
    Tendsto delta atTop (nhds 0) →
    ∃ error : ℕ → ℝ,
      (∀ L : ℕ, 0 ≤ error L) ∧
      Tendsto (fun L : ℕ => error L / (L : ℝ)) atTop (nhds 0) ∧
      ¬ Tendsto
        (fun L : ℕ => error L / ((L : ℝ) * delta L)) atTop (nhds 0)

end MathlibPlus.Open.ResearchFormalization.ShrinkingActionGapRequiresScaledMargin15412
