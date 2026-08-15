import Mathlib

namespace MathlibPlus.Open.Analysis.K0127

/-- Claim 8924: the logarithmic ratio observable is bounded and continuous on the
nonnegative half-line, and has limit zero at positive infinity. -/
def claim8924 : Prop :=
  ∀ (s s₀ : ℝ),
    0 < s →
    0 < s₀ →
    let f : ℝ → ℝ := fun z => Real.log ((s + z ^ 2) / (s₀ + z ^ 2))
    (∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, z ∈ Set.Ici 0 → |f z| ≤ C) ∧
      ContinuousOn f (Set.Ici 0) ∧
      Filter.Tendsto f Filter.atTop (nhds 0)

end MathlibPlus.Open.Analysis.K0127
