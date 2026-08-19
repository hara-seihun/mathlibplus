import MathlibPlus.GraphTheory.CayleyCIHierarchy
import MathlibPlus.Open.Research.R1378Batch
import MathlibPlus.Open.ResearchFormalization.R1171Claim41590

namespace MathlibPlus.Open.ResearchFormalization.R1636Claim39825

open MathlibPlus.GraphTheory
open MathlibPlus.Open.Research.R1378
open MathlibPlus.Open.ResearchFormalization.R1171Claim41590

/-- Binary-relational CI for the prime-by-square-free cyclic product, together
with the exact 2-closed regular-copy formulation. -/
def binaryRelationalCIPrimeSquarefreeProduct_claim39825 : Prop :=
  ∀ (p n : ℕ) (hp : Nat.Prime p) (hn : 0 < n), Squarefree n →
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let G := Multiplicative (ZMod p) × Multiplicative (ZMod n)
    IsCayleyCI2 G ∧
      (∀ (X : Subgroup (Equiv.Perm G)),
        (rightRegular : Subgroup (Equiv.Perm G)) ≤ X →
          twoClosedAmbient X →
            ∀ (R T : Subgroup (Equiv.Perm G)),
              R ≤ X → T ≤ X →
                IsRegularCopy G R → IsRegularCopy G T →
                  conjugateInAmbient X R T)

end MathlibPlus.Open.ResearchFormalization.R1636Claim39825
