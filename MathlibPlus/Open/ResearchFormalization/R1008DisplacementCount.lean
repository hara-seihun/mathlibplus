import MathlibPlus.Open.ResearchFormalization.Lease01a0019fGroup

namespace MathlibPlus.Open.ResearchFormalization.R1008DisplacementCount

noncomputable section

abbrev B3 := MathlibPlus.Open.ResearchFormalization.Batch01.B3

/-- Claim 28199: the exact proper/full displacement-span census over all
permutations of the nine-point carrier `C₃²`. -/
def exactProperDisplacementPermutationCount_claim28199 : Prop :=
  Nat.card (Equiv.Perm B3) = Nat.factorial 9 ∧
    Nat.card {p : Equiv.Perm B3 //
      MathlibPlus.Open.ResearchFormalization.Batch01.normalizedDisplacement p ≠
        (⊤ : AddSubgroup B3)} = 2565 ∧
    Nat.card {p : Equiv.Perm B3 //
      MathlibPlus.Open.ResearchFormalization.Batch01.normalizedDisplacement p =
        (⊤ : AddSubgroup B3)} = 360315

end

end MathlibPlus.Open.ResearchFormalization.R1008DisplacementCount
