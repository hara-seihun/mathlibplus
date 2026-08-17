import MathlibPlus.Open.ResearchFormalization.R1212

namespace MathlibPlus.Open.ResearchFormalization.R1212Claim42067

open MathlibPlus.Open.ResearchFormalization.R1212

/-- Claim 42067: the exact normalized C_p × A₄ common-coordinate profile has
one nonidentity nonlinear chart and unrestricted translations on every other
base point. -/
def claim42067 {p : ℕ}
    (q : Equiv.Perm A4)
    (σ : A4 → Equiv.Perm (ZMod p))
    (f : Equiv.Perm (ProductGroup p)) : Prop :=
  Nat.Prime p ∧
    5 ≤ p ∧
      normalizedCommonCoordinateMap q σ f ∧
        ∃ a : A4, singletonNonlinearChart σ a

end MathlibPlus.Open.ResearchFormalization.R1212Claim42067
