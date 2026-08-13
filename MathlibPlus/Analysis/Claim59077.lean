import Mathlib

namespace MathlibPlus.Analysis.Claim59077

/-- The numerical margin in claim 59077 already rules out a majorant below
one, even before the nonnegative derivative-residual term is added. -/
theorem separatedAbsoluteMajorant
    (U₀ U₁ : ℝ)
    (hmargin : 1 - U₀ <
      -(0.0029377440723083452325379135290641512 : ℝ))
    (hU₁ : 0 ≤ U₁) :
    ¬ U₀ + U₁ < 1 := by
  intro hlt
  linarith

end MathlibPlus.Analysis.Claim59077
