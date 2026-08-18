import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1052Claim28513

noncomputable section

open Classical
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def binaryBlockSystem
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (blocks : Finset (Finset Ω)) : Prop :=
  (∀ B ∈ blocks, B.card = 2) ∧
    (∀ B ∈ blocks, ∀ C ∈ blocks, B = C ∨ Disjoint B C) ∧
    blocks.biUnion id = Finset.univ

noncomputable def preservesBlocks
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A : Subgroup (Equiv.Perm Ω))
    (blocks : Finset (Finset Ω)) : Prop :=
  ∀ a : A, ∀ B ∈ blocks,
    ∃ C ∈ blocks,
      (a : Equiv.Perm Ω) '' (B : Set Ω) = (C : Set Ω)

noncomputable def blockKernelCondition
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A : Subgroup (Equiv.Perm Ω))
    (blocks : Finset (Finset Ω)) (k : Equiv.Perm Ω) : Prop :=
  k ∈ A ∧ ∀ B ∈ blocks, k '' (B : Set Ω) = (B : Set Ω)

abbrev BlockIndex {Ω : Type*} (blocks : Finset (Finset Ω)) :=
  {B : Finset Ω // B ∈ blocks}

abbrev BlockPermutationProduct {Ω : Type*}
    (blocks : Finset (Finset Ω)) :=
  ∀ B : BlockIndex blocks, Equiv.Perm B.1

abbrev BinaryPower (m : ℕ) := Fin m → ZMod 2

/-- The block-action kernel has its faithful restriction homomorphism into the
product of the symmetric groups of the actual two-point blocks, and that
product is a copy of `C₂^m`. -/
def faithfulBinaryBlockKernelEmbedding_claim28513 : Prop :=
  ∀ {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A : Subgroup (Equiv.Perm Ω))
    (blocks : Finset (Finset Ω)) (m : ℕ),
    binaryBlockSystem blocks →
    blocks.card = m →
    preservesBlocks A blocks →
      ∃ K : Subgroup (Equiv.Perm Ω),
        (∀ k : Equiv.Perm Ω,
          k ∈ K ↔ blockKernelCondition A blocks k) ∧
        ∃ restriction : K →* BlockPermutationProduct blocks,
          Function.Injective restriction ∧
          (∀ (k : K) (B : BlockIndex blocks) (x : B.1),
            ((restriction k) B x : Ω) = (k : Equiv.Perm Ω) x) ∧
          Nonempty (BlockPermutationProduct blocks ≃* BinaryPower m)

end

end MathlibPlus.Open.ResearchFormalization.R1052Claim28513
