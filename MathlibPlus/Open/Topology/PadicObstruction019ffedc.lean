import Mathlib

namespace MathlibPlus.Open.Topology.Padic

/-- Claim 11592: no continuous unital ring homomorphism from ℚ_p to ℂ. -/
def noContinuousUnitalMapQpToC (p : ℕ) [Fact (Nat.Prime p)] : Prop :=
  ¬ ∃ f : Padic p →+* ℂ, Continuous f

end MathlibPlus.Open.Topology.Padic
