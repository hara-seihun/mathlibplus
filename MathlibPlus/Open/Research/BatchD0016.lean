import Mathlib

namespace MathlibPlus.Open.ResearchBatch.D0016

noncomputable def unitPhase (x : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0
  else Complex.exp (Complex.I * (x : ℂ) * (Real.log (n : ℝ) : ℂ))

def basicUnitPhaseValuesAndNonvanishing_claim : Prop :=
  ∀ x : ℝ,
    unitPhase x 0 = 0 ∧
    unitPhase x 1 = 1 ∧
    ∀ n : ℕ, n ≠ 0 → unitPhase x n ≠ 0

end MathlibPlus.Open.ResearchBatch.D0016
