import MathlibPlus.Open.ResearchFormalization.R1181Suborbit

namespace MathlibPlus.Open.ResearchFormalization.R1181Claim31923

/-- Claim 31923: a finite displayed internal direct product of nonabelian
simple permutation factors has pairwise disjoint block supports partitioning
the preserved block partition, with each factor acting transitively and
setwise on its supported blocks and trivially outside its support. -/
def claim31923 {Ω : Type} {r : ℕ}
    (G M : Subgroup (Equiv.Perm Ω))
    (T : Fin r → Subgroup (Equiv.Perm Ω))
    (P : Set (Set Ω)) (C : Fin r → Set (Set Ω)) : Prop :=
  MathlibPlus.Open.ResearchFormalization.R1181Suborbit.blockPartition P ∧
    MathlibPlus.Open.ResearchFormalization.R1181Suborbit.transitiveOn
      G Set.univ ∧
      MathlibPlus.Open.ResearchFormalization.R1181Suborbit.preservesBlocks
        G P ∧
        MathlibPlus.Open.ResearchFormalization.R1181Suborbit.normalIn M G ∧
        MathlibPlus.Open.ResearchFormalization.R1181Suborbit.internalDirectProduct
          M T ∧
        (∀ i, MathlibPlus.Open.ResearchFormalization.R1181Suborbit.nonabelianSimpleFactor
          (T i)) ∧
        MathlibPlus.Open.ResearchFormalization.R1181Suborbit.blockPartPartition
          C P ∧
        (∀ i,
          MathlibPlus.Open.ResearchFormalization.R1181Suborbit.supportOf (T i) =
            ⋃₀ (C i)) ∧
        (∀ i, ∀ h : T i, ∀ x,
          x ∉ MathlibPlus.Open.ResearchFormalization.R1181Suborbit.supportOf
            (T i) →
            (h : Equiv.Perm Ω) x = x) ∧
        (∀ i, ∀ B, B ∈ C i →
          ∀ h : T i, (h : Equiv.Perm Ω) '' B = B) ∧
        (∀ i, ∀ B, B ∈ C i →
          MathlibPlus.Open.ResearchFormalization.R1181Suborbit.transitiveOn
            (T i) B)

end MathlibPlus.Open.ResearchFormalization.R1181Claim31923
