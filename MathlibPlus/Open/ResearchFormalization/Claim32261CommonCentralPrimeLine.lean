import MathlibPlus.Open.Research.CommonCentralPrimeLine

namespace MathlibPlus.Open.ResearchFormalization.Claim32261

open MathlibPlus.Open.Research.CommonCentralPrimeLine

/-- Claim 32261: a common literal complement produces, after a centralizing
conjugation, one common central prime-line block system for the two regular
 direct products. -/
def regularDirectProductsAcquireCommonCentralBlockSystem_claim32261 : Prop :=
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
    regularDirectProduct P L →
    regularDirectProduct Q L →
    ∃ k : A, k ∈ π.ker ∧
      (∀ l : L, conjugateBy k (l : A) = (l : A)) ∧
      ∃ D : Subgroup A,
        D ≤ P ∧
        (∀ d : D, ∃ q : Q,
          (d : D) = conjugateBy k ((q : Q) : A)) ∧
        Nat.card D = p ∧
        centralSubgroupIn D (P ⊔ L) ∧
        centralSubgroupIn D (conjugatedCopy Q L k) ∧
        commonPrimeLineOrbitSystem D (P ⊔ L)
          (conjugatedCopy Q L k) p

end MathlibPlus.Open.ResearchFormalization.Claim32261
