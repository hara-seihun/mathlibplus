import MathlibPlus.Open.Research.LaplaceBatch

open MeasureTheory

namespace MathlibPlus.Open.Research

noncomputable section

/-- The actual Laplace transform used by the positive-real setup. -/
def positiveRealLaplaceTransform (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ u in Set.Ici 0, (f u : ℂ) * Complex.exp (-z * (u : ℂ))

/-- The pointwise peak conclusion for the Laplace carrier from the preceding
positive-real setup. -/
def positiveRealLaplaceKernelPeaksAtOrigin : Prop :=
  ∀ f : ℝ → ℝ, positiveRealLaplaceSetup f →
    ∀ u : ℝ, 0 ≤ u → 0 ≤ f u ∧ f u ≤ f 0

/-- The real-axis endpoint estimate and its zero-endpoint consequence for the
same positive-real Laplace carrier. -/
def positiveRealLaplaceEndpointMassBound : Prop :=
  ∀ f : ℝ → ℝ, positiveRealLaplaceSetup f →
    (∀ x : ℝ, 0 < x →
      (positiveRealLaplaceTransform f (x : ℂ)).re ≤ f 0 / x) ∧
      (f 0 = 0 → ∀ u : ℝ, 0 ≤ u → f u = 0)

end
end MathlibPlus.Open.Research
