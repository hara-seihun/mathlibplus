import MathlibPlus.Open.ResearchFormalization.R1153

namespace MathlibPlus.Open.ResearchFormalization.R1153Claim41382

open MathlibPlus.Open.ResearchFormalization.R1153

/-- Claim 41382: a minimum nontrivial block system gives primitive induced
local action, while the local block-kernel image is transitive and normal and
contains the regular block-kernel intersection image. -/
def claim41382 : Prop :=
  ∀ {A : Type*} [Fintype A] [CommGroup A],
    Odd (Fintype.card A) →
    ∀ (Ω : Type*) [Fintype Ω]
      (X : Subgroup (Equiv.Perm Ω))
      (R T : Subgroup X)
      (B : Finset (Set Ω))
      (π : X →* Equiv.Perm (BlockType B)),
      Nonempty (R ≃* (A × Q8)) →
      Nonempty (T ≃* (A × Q8)) →
      MathlibPlus.Open.GraphTheory.regularPermutationSubgroup
        (R.map X.subtype) →
      MathlibPlus.Open.GraphTheory.regularPermutationSubgroup
        (T.map X.subtype) →
      Subgroup.closure ((R : Set X) ∪ (T : Set X)) = ⊤ →
      commonNontrivialBlockSystem B →
      (∀ (x : X) (U : BlockType B),
        ((π x) U).1 = ((x : Equiv.Perm Ω) '' U.1)) →
      MathlibPlus.Open.ResearchFormalization.minimumNontrivialBlockSystem
          (X : Set (Equiv.Perm Ω)) (B : Set (Set Ω)) →
      (∀ U : BlockType B,
        MathlibPlus.Open.ResearchFormalization.primitivePermutationSet
          (MathlibPlus.Open.ResearchFormalization.inducedLocalPermutations
            (X : Set (Equiv.Perm Ω)) U.1)) ∧
      (∀ U : BlockType B,
        localKernelImageNormalTransitive31619
          (MathlibPlus.Open.ResearchFormalization.inducedLocalPermutations
            (X : Set (Equiv.Perm Ω)) U.1)
          (localKernelImage31619 π U)
          (localIntersectionImage31619 π R U))

end MathlibPlus.Open.ResearchFormalization.R1153Claim41382
