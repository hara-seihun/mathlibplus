import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0227Claim19008

/-- Claim 19008: a supplied family-valued carrier agrees with the displayed
    adversarial entire-function formula on the source's parameter domain. -/
def adversarialEntireFunctionFamily_claim19008
    (A : ℝ → ℝ → ℂ → ℂ) : Prop :=
  ∀ (a c : ℝ) (z : ℂ), 0 < a → 1 < c →
    A a c z = (c : ℂ) + Complex.cosh ((a : ℂ) * z)

end MathlibPlus.Open.ResearchFormalization.R0227Claim19008
