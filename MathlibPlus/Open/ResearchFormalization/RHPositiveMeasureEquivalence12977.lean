import MathlibPlus.Open.ResearchFormalization.Claims12988_12990

namespace MathlibPlus.Open.ResearchFormalization.RHPositiveMeasureEquivalence12977

open MathlibPlus.Open.ResearchFormalization MeasureTheory

/-- RH is equivalent to the common small-positive-frequency direct positive
measure representation on the stated slit plane. -/
def claim12977 : Prop :=
  RiemannHypothesis ↔
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ t : ℝ, 0 < t → t < t₀ →
        ∃! μ : Measure ℝ,
          DirectStieltjesRepresentation t μ

end MathlibPlus.Open.ResearchFormalization.RHPositiveMeasureEquivalence12977
