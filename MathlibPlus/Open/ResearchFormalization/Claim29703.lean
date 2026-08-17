import MathlibPlus.Open.Research.BatchDerivative

namespace MathlibPlus.Open.ResearchFormalization.Claim29703

open MathlibPlus.Open.Research.BatchDerivative

/-- Claim 29703: every normalized permutation of `C₃²` has one common linear
shadow for all generated derivative orbits, and the complete normalized
permutation census has the four stated orbit-shape/shadow rows. -/
def claim29703 : Prop :=
  (∀ σ : Equiv.Perm H3, normalized σ → hasLinearShadow σ) ∧
    Set.ncard normalizedPermutations = 40320 ∧
    Set.ncard {σ : Equiv.Perm H3 |
      σ ∈ normalizedPermutations ∧
        orbitShape_1_9 σ ∧ shadowCount σ = 1} = 48 ∧
    Set.ncard {σ : Equiv.Perm H3 |
      σ ∈ normalizedPermutations ∧
        orbitShape_1_3_3_2 σ ∧ shadowCount σ = 3} = 384 ∧
    Set.ncard {σ : Equiv.Perm H3 |
      σ ∈ normalizedPermutations ∧
        orbitShape_1_2_3_2 σ ∧ shadowCount σ = 6} = 1728 ∧
    Set.ncard {σ : Equiv.Perm H3 |
      σ ∈ normalizedPermutations ∧
        orbitShape_1_8 σ ∧ shadowCount σ = 48} = 38160

end MathlibPlus.Open.ResearchFormalization.Claim29703
