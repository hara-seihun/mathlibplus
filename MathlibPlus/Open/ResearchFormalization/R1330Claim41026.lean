import MathlibPlus.Open.Research.R1330Claim41037

namespace MathlibPlus.Open.ResearchFormalization.R1330Claim41026

open MathlibPlus.Open.Research.R1330Formalization_41037

noncomputable section

/-- Claim 41026: for each odd prime, the concrete six-block construction has
 the full two-coordinate alternating kernel and the resulting group order. -/
def claim41026 : Prop :=
  ∀ p : ℕ, ∀ hp : Nat.Prime p, Odd p →
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∃ F : Equiv.Perm (Ω p),
      (∀ z : Ω p, F z = blockShear p z) ∧
        fullProductKernel p F ∧
          Nat.card (generatedGroup p F) =
            6 * (Nat.card (alternatingGroup (V p))) ^ 2

end

end MathlibPlus.Open.ResearchFormalization.R1330Claim41026
