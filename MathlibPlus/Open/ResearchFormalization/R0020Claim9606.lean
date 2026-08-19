import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0020Claim9606

private def gripfallFactor (m : ℕ) (z : ℂ) : ℂ :=
  1 + z ^ (4 * m)

/-- Claim 9606: the exact Gripfall factor `Q_m(z) = 1 + z^(4m)` is even
in its complex argument for every depth. -/
def gripfallFactor_even_claim9606 : Prop :=
  ∀ (m : ℕ) (z : ℂ),
    gripfallFactor m (-z) = gripfallFactor m z

end MathlibPlus.Open.ResearchFormalization.R0020Claim9606
