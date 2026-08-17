import MathlibPlus.Open.Research.R1330Claim41037

namespace MathlibPlus.Open.ResearchFormalization.R1330GeneratedKernel41025

noncomputable section

open MathlibPlus.Open.Research.R1330Formalization_41037

def regularPermutationSubgroup {p : ℕ}
    (R : Subgroup (Equiv.Perm (Ω p))) : Prop :=
  ∀ x y : Ω p, ∃! r : R, r.1 x = y

/-- Claim 41025: the exact Record-12 carrier consists of the natural
regular copy, its block-shear conjugate, the generated pair group, and the
kernel of that group on the six `V`-blocks. -/
def claim41025 : Prop :=
  ∀ (p : ℕ),
    Nat.Prime p →
      Odd p →
        ∃ F : Equiv.Perm (Ω p),
          (∀ z : Ω p, F z = blockShear p z) ∧
            let R := regularCopy p
            let T := conjugateSubgroup F R
            let M := generatedGroup p F
            regularPermutationSubgroup R ∧
              regularPermutationSubgroup T ∧
                T = conjugateSubgroup F R ∧
                  M = generatedGroup p F ∧
                    (∀ k : Equiv.Perm (Ω p),
                      blockKernel p F k ↔
                        k ∈ M ∧ fixesBlocks k) ∧
                      (∀ H : Subgroup (Equiv.Perm (Ω p)),
                        R ≤ H → T ≤ H → M ≤ H)

end

end MathlibPlus.Open.ResearchFormalization.R1330GeneratedKernel41025
