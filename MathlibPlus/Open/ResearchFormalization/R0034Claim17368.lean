import MathlibPlus.Open.ResearchFormalization.R0034Claims17371_17372

open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.R0034Claim17368

noncomputable section

/-- Claim 17368: the gamma channel has rising-factorial moments. -/
def claim17368 : Prop :=
  ∀ α β : ℝ, β = α + (1 : ℝ) / 2 → 0 ≤ β →
    ∀ r : ℕ,
      ∫ y : ℝ, y ^ r ∂(
        MathlibPlus.Open.ResearchFormalization.R0034Claims17371_17372.gammaMeasure β) =
        MathlibPlus.Open.NewResearch2.R0033.risingFactorial β r

end

end MathlibPlus.Open.ResearchFormalization.R0034Claim17368
