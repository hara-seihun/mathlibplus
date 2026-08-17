import MathlibPlus.Open.Research.R1330Claim41037

namespace MathlibPlus.Open.ResearchFormalization.R1330Claim41024

noncomputable section

open MathlibPlus.Open.Research.R1330Formalization_41037

/-- The exact six-block chart specified by Claim 41024 exists as a
permutation on the displayed `V × S₃` carrier for every odd prime. -/
def claim41024 : Prop :=
  ∀ p : ℕ, Nat.Prime p → Odd p →
    ∃ F : Equiv.Perm (Ω p),
      ∀ z : Ω p, F z = blockShear p z

end

end MathlibPlus.Open.ResearchFormalization.R1330Claim41024
