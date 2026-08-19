import Mathlib

namespace MathlibPlus.Open.Analysis.Claim5977

noncomputable section

/-- The heat-log moment family on its stated positive domain. -/
noncomputable def heatLogMoment_claim5977
    (t σ : ℝ) (j : ℕ) (v : Set.Ioi (0 : ℝ)) : ℝ :=
  (Real.log v.1) ^ j *
    Real.exp ((t / 4) * (Real.log v.1) ^ 2 - σ * Real.log v.1)

end
end MathlibPlus.Open.Analysis.Claim5977
