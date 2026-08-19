import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0103Claim17965

/-- Claim 17965: multiplication by the green factor cancels the Mellin pole
factor away from its two poles. -/
def claim17965 : Prop :=
  ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
    let B : ℂ := 1 / (s * (s - 1))
    let g : ℂ := s * (s - 1)
    g * B = 1

end MathlibPlus.Open.ResearchFormalization.R0103Claim17965
