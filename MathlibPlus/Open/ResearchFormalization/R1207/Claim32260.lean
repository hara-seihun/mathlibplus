import MathlibPlus.Open.Research.SylowPropagationPrimeLine

namespace MathlibPlus.Open.ResearchFormalization.R1207.Claim32260

open MathlibPlus.Open.Research.SylowPropagationPrimeLine

def sylowConjugacyAndTransitivePropagation_claim32260 : Prop :=
  ∀ (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (B : Finset (Set Ω))
    (A : Subgroup (Permutation Ω))
    (π : A →* Equiv.Perm (MathlibPlus.Open.blockType B))
    (p : ℕ) (P Q L : Subgroup A),
    validBlockAction B A π →
    Nat.Prime p →
    regularKernelCopy π P →
    regularKernelCopy π Q →
    abelianCopy P →
    abelianCopy Q →
    permutationPGroup p P →
    permutationPGroup p Q →
    transitiveLiteralComplement π L →
    (∀ q : Q, centralizesLiteral (q : A) L) →
    (∀ q : P, centralizesLiteral (q : A) L) →
    sylowPropagationConclusion π p P Q L

end MathlibPlus.Open.ResearchFormalization.R1207.Claim32260
