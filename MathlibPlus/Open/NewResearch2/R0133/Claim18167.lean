import Mathlib

open scoped Interval

namespace MathlibPlus.Open.NewResearch2.R0133

noncomputable section

/-- Claim 18167: the endpoint deficit defined by the Gaussian cell integral has
its positive integral representation, together with strict positivity at a
positive heat scale. -/
def claim18167_positiveIntegralRepresentationEndpointDeficit : Prop :=
  ∀ (n : ℕ) (c : ℝ), 0 < c →
    (((∫ t in (n : ℝ)..((n : ℝ) + 1),
        Real.exp (-c * t ^ 2)) -
        Real.exp (-c * ((n : ℝ) + 1) ^ 2)) =
      ∫ t in (n : ℝ)..((n : ℝ) + 1),
        (t - (n : ℝ)) * (2 * c * t) * Real.exp (-c * t ^ 2)) ∧
    0 < (∫ t in (n : ℝ)..((n : ℝ) + 1),
        Real.exp (-c * t ^ 2)) -
      Real.exp (-c * ((n : ℝ) + 1) ^ 2)

end

end MathlibPlus.Open.NewResearch2.R0133
