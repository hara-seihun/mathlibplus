import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R4434Claim52204

noncomputable section

/-- The exact retained fine-block and outer-ratio phase-width inequalities. -/
def fineBlockPhaseWidth_claim52204 : Prop :=
  let X : ℝ := 6000000185827
  ∀ x : ℝ, X < x →
    (x / 2) * Real.log (10001 / 10000) > X / 20002 ∧
      X / 20002 > 3 * 10 ^ 8 ∧
      Real.log 40 > 1 ∧
      (x / 2) * Real.log 40 > X / 2

end

end MathlibPlus.Open.ResearchFormalization.R4434Claim52204
