import MathlibPlus.Open.ResearchFormalization.R1153
import MathlibPlus.Open.ResearchFormalizationBatch.R1153BlockKernel41380

namespace MathlibPlus.Open.ResearchFormalization.R1153Claim41381

open MathlibPlus.Open.ResearchFormalization.R1153
open MathlibPlus.Open.ResearchFormalization.R1153BlockKernel41380

/-- The exact four-form subgroup/quotient disjunction on the actual block
kernel and regular quotient. -/
def exactFourFormTaxonomy
    {A : Type*} [CommGroup A]
    (H Q : Type*) [Group H] [Group Q] : Prop :=
  ∃ C : Subgroup A,
    oneOfFour31618
      (Nonempty (H ≃* C) ∧
        Nonempty (Q ≃* ((A ⧸ C) × Q8)))
      (Nonempty (H ≃* (C × ZMod 2)) ∧
        Nonempty (Q ≃* ((A ⧸ C) × (ZMod 2 × ZMod 2))))
      (Nonempty (H ≃* (C × ZMod 4)) ∧
        Nonempty (Q ≃* ((A ⧸ C) × ZMod 2)))
      (Nonempty (H ≃* (C × Q8)) ∧
        Nonempty (Q ≃* (A ⧸ C))) ∧
    ¬ Nonempty (H ≃* (ZMod 2 × ZMod 2))

/-- Claim 41381: every actual regular-copy block kernel and its actual regular
quotient has exactly one of the four listed forms, and the elementary
`C₂²` block subgroup is excluded. -/
def claim41381 : Prop :=
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
        ∀ S : Subgroup X, S = R ∨ S = T →
          MathlibPlus.Open.regularSubgroupOnBlocks (S.map π) →
            exactFourFormTaxonomy (A := A)
              (↥(kernelIntersection31617 π S)) (↥(S.map π))

end MathlibPlus.Open.ResearchFormalization.R1153Claim41381
