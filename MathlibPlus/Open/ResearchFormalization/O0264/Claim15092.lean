import Mathlib
import MathlibPlus.Open.Research.FormalizationBatchO0264

open Filter MeasureTheory Set
open scoped Topology

namespace MathlibPlus.Open.ResearchFormalization.O0264

noncomputable section

open MathlibPlus.Open.Research.FormalizationBatchO0264

abbrev ComplexScaleMeasure15092 := MeasureTheory.ComplexMeasure ℝ

def totalVariationNorm15092 (μ : ComplexScaleMeasure15092) : ℝ :=
  ENNReal.toReal ((VectorMeasure.variation μ) Set.univ)

def boundedIntervalMeasureFamily15092
    (μ : ℝ → ComplexScaleMeasure15092)
    (a b D : ℝ → ℝ) (D₀ : ℝ) : Prop :=
  0 ≤ D₀ ∧
    ∀ N : ℝ, 1 < N →
      IsFiniteMeasure (VectorMeasure.variation (μ N)) ∧
        μ N Set.univ = (1 : ℂ) ∧
          a N ≤ b N ∧
            0 ≤ D N ∧
              D N ≤ D₀ ∧
                b N - a N = D N ∧
                  (VectorMeasure.variation (μ N))
                      (Set.Icc (a N) (b N))ᶜ = 0

noncomputable def familyPacketEnergy15092
    (ρ : ℂ) (μ : ℝ → ComplexScaleMeasure15092) (N : ℝ) : ℝ :=
  pointSupportedPacketEnergy ρ N (μ N)

def familyVariation15092
    (μ : ℝ → ComplexScaleMeasure15092) (N : ℝ) : ℝ :=
  totalVariationNorm15092 (μ N)

def claim15092_boundedVariationCannotBeatLogSuppression : Prop :=
  ∀ (ρ : ℂ) (μ : ℝ → ComplexScaleMeasure15092)
    (a b D : ℝ → ℝ) (D₀ : ℝ),
    certifiedSimpleCriticalZero ρ →
      boundedIntervalMeasureFamily15092 μ a b D D₀ →
        ((fun N : ℝ => familyPacketEnergy15092 ρ μ N) =o[atTop]
          (fun N : ℝ => 1 / Real.log N) →
          Tendsto (fun N : ℝ => familyVariation15092 μ N)
            atTop atTop) ∧
        (∀ V₀ : ℝ,
          0 ≤ V₀ →
            (∀ N : ℝ, 1 < N → familyVariation15092 μ N ≤ V₀) →
              ∃ c : ℝ, 0 < c ∧
                ∀ᶠ N : ℝ in atTop,
                  c / Real.log N ≤ familyPacketEnergy15092 ρ μ N)

end

end MathlibPlus.Open.ResearchFormalization.O0264
