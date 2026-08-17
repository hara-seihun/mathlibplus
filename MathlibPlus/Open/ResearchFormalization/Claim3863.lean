import MathlibPlus.Open.Analysis.FixedAnnulusWeakStarZero3867

namespace MathlibPlus.Open.ResearchFormalization.Claim3863

noncomputable section

open Set
open MathlibPlus.Open.Analysis.FixedAnnulusWeakStarZero

/-- Claim 3863: an integrable source supported on a fixed positive compact
annulus has an entire Mellin transform, with the reviewed complex-power
convention. -/
def compactAnnulusMellinEntire3863 : Prop :=
  ∀ (a b : ℝ) (p : ℝ → ℂ),
    0 < a →
    a ≤ b →
    Function.support p ⊆ Icc a b →
    MeasureTheory.IntegrableOn p (Icc a b) →
    Differentiable ℂ (intervalMellin3867 a b p)

end

end MathlibPlus.Open.ResearchFormalization.Claim3863
