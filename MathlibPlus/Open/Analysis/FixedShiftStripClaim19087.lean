import MathlibPlus.Open.Analysis.VerticalShiftExact

namespace MathlibPlus.Open.Analysis.Claim19087

open MathlibPlus.Open.Analysis.Claim19067
open MathlibPlus.Open.Analysis.VerticalShiftExact

noncomputable section

/-- Fixed-shift contraction of a zero strip for the vertical real-part average. -/
def fixedShiftStripContraction_claim19087 : Prop :=
  ∀ τ Δ ω : ℝ, 0 ≤ Δ → 0 ≤ ω →
    let F : EntireFunction := literalHeatTransform τ
    let A : EntireFunction := verticalAverage F ω
    (∀ ρ : ℂ, F ρ = 0 → |ρ.im| ≤ Δ) →
      (∀ z : ℂ, A z = 0 →
        |z.im| ≤ Real.sqrt (max (Δ ^ 2 - ω ^ 2) 0)) ∧
      (Δ = 1 → 1 ≤ ω → realRootedFunction A)

end
end MathlibPlus.Open.Analysis.Claim19087
