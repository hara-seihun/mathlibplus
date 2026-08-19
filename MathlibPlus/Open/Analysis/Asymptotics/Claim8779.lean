import Mathlib

namespace MathlibPlus.Open.Analysis.Asymptotics

/-- Claim 8779: the regularly varying terminal action is strictly positive
on the full source interval `0<τ<1`. -/
def regularlyVaryingActionPositivity : Prop :=
  ∀ τ : ℝ, 0 < τ → τ < 1 →
    0 < ((2 - τ) / 2) * Real.log ((2 - τ) / τ) - 1 + τ

end MathlibPlus.Open.Analysis.Asymptotics
