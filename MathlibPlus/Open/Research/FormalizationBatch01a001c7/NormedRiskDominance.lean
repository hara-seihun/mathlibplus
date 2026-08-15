import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch01a001c7

/-- Claim 59994: the pointwise norm-square lower bound and its two consequences. -/
def normedRiskDominance : Prop :=
  ∀ (V W : Type*) [NormedAddCommGroup W]
    (L : V → W) (B R : V → ℝ),
    (∀ v, B v ≤ -((1 : ℝ) / 16) * ‖L v‖ ^ 2) →
    (∀ v, 0 ≤ B v + R v) →
      (∀ v, R v ≥ ((1 : ℝ) / 16) * ‖L v‖ ^ 2) ∧
      (∀ v, L v ≠ 0 → R v > 0) ∧
      (∀ v, R v = 0 → L v = 0)

end MathlibPlus.Open.Research.FormalizationBatch01a001c7
