import Mathlib

namespace MathlibPlus.Open.Research

/-- The paired vertical-cone factor from Claim 42859. -/
noncomputable def pairedVerticalConeFactor (ρ : ℂ) (h : ℝ) : ℂ :=
  1 + (h : ℂ) ^ 2 / ρ ^ 2

end MathlibPlus.Open.Research
