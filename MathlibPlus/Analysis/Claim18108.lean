import Mathlib

namespace MathlibPlus.Analysis.Claim18108

noncomputable section

/-- The backward-sample moment from claim 18108.  The displayed real
integral is recorded as an object; no separate convergence or evaluation
claim is asserted here. -/
def backwardSampleMoment (n k : ℕ) : ℝ :=
  ∫ x in Set.Icc (n : ℝ) ((n + 1 : ℕ) : ℝ),
    (x - n) * Real.rpow x (-((3 : ℝ) / 2) - 2 * k)

end

end MathlibPlus.Analysis.Claim18108
