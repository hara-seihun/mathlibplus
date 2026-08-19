import Mathlib
import MathlibPlus.Open.ResearchFormalization.O0264.Claim15092

open scoped Topology
open Filter MeasureTheory

open MathlibPlus.Open.Research.FormalizationBatchO0264

namespace MathlibPlus.Open.ResearchFormalization.O0264

noncomputable section

/-- Claim 15093: an eventual power improvement over the logarithmic packet
scale forces the quantitative power growth of the exact total variation. -/
def claim15093_powerImprovementRequiresPowerGrowth : Prop :=
  ∀ (ρ : ℂ) (μ : ℝ → ComplexScaleMeasure15092)
    (a b D : ℝ → ℝ) (D₀ η C : ℝ),
    certifiedSimpleCriticalZero ρ →
    boundedIntervalMeasureFamily15092 μ a b D D₀ →
    0 < η →
    0 < C →
    (∀ N : ℝ, 1 < N → 0 < D N) →
    (∀ᶠ N : ℝ in atTop,
      1 < N →
        familyPacketEnergy15092 ρ μ N ≤
          C * Real.rpow (Real.log N) (-1 - η)) →
    ∀ᶠ N : ℝ in atTop,
      1 < N →
        Real.rpow (Real.log N) η /
            (16 * Real.pi * C * ‖ρ‖ ^ 2 * D N) ≤
          familyVariation15092 μ N

end

end MathlibPlus.Open.ResearchFormalization.O0264
