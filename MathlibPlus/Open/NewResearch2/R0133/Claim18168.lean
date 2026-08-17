import Mathlib

open scoped Interval

namespace MathlibPlus.Open.NewResearch2.R0133

noncomputable section

/-- Claim 18168: the first cell moment is the endpoint deficit divided by
 twice the positive heat scale. -/
def claim18168_firstCellMomentIdentity : Prop :=
  ∀ (n : ℕ) (c : ℝ), 0 < c →
    (∫ x in (n : ℝ)..((n : ℝ) + 1),
      x * (x - (n : ℝ)) * Real.exp (-c * x ^ 2)) =
      ((∫ x in (n : ℝ)..((n : ℝ) + 1),
        Real.exp (-c * x ^ 2)) -
        Real.exp (-c * ((n : ℝ) + 1) ^ 2)) / (2 * c)

end

end MathlibPlus.Open.NewResearch2.R0133
