import Mathlib

namespace MathlibPlus.Open.NewResearch2.R1052RegularAbelianKernel

noncomputable section

private def binaryBlockSystem {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (blocks : Finset (Finset Ω)) : Prop :=
  (∀ B ∈ blocks, B.card = 2) ∧
    (∀ B ∈ blocks, ∀ C ∈ blocks, B = C ∨ Disjoint B C) ∧
    blocks.biUnion id = Finset.univ

private def preservesBlocks {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A : Subgroup (Equiv.Perm Ω))
    (blocks : Finset (Finset Ω)) : Prop :=
  ∀ a : A, ∀ B ∈ blocks,
    ∃ C ∈ blocks,
      (a : Equiv.Perm Ω) '' (B : Set Ω) = (C : Set Ω)

private def regularAbelian {Ω : Type*} [Fintype Ω]
    (R : Subgroup (Equiv.Perm Ω)) : Prop :=
  (∀ x y : R, (x : Equiv.Perm Ω) * (y : Equiv.Perm Ω) =
      (y : Equiv.Perm Ω) * (x : Equiv.Perm Ω)) ∧
    (∀ x y : Ω, ∃! r : R, (r : Equiv.Perm Ω) x = y)

private def blockKernel {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A : Subgroup (Equiv.Perm Ω))
    (blocks : Finset (Finset Ω)) : Set (Equiv.Perm Ω) :=
  {a | a ∈ A ∧ ∀ B ∈ blocks, a '' (B : Set Ω) = (B : Set Ω)}

private def kernelIntersection {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A R : Subgroup (Equiv.Perm Ω))
    (blocks : Finset (Finset Ω)) :=
  {r : R // (r : Equiv.Perm Ω) ∈ blockKernel A blocks}

private def regularOnEachBlock {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A R : Subgroup (Equiv.Perm Ω))
    (blocks : Finset (Finset Ω)) : Prop :=
  ∀ B ∈ blocks, ∀ x y : Ω, x ∈ B → y ∈ B →
    ∃! r : kernelIntersection A R blocks,
      (r.1 : Equiv.Perm Ω) x = y

private def uniqueNonidentityFixedPointFree
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A R : Subgroup (Equiv.Perm Ω))
    (blocks : Finset (Finset Ω)) : Prop :=
  ∃ δ : kernelIntersection A R blocks,
    (δ.1 : Equiv.Perm Ω) ≠ 1 ∧
      (∀ x : Ω, (δ.1 : Equiv.Perm Ω) x ≠ x) ∧
      (∀ ε : kernelIntersection A R blocks,
        (ε.1 : Equiv.Perm Ω) ≠ 1 → ε = δ)

/-- Claim 28515: a regular abelian subgroup lying in the block-preserving
permutation group meets the literal two-point block kernel in order two,
acts regularly on every block, and has a unique nonidentity fixed-point-free
intersection element. -/
def regularAbelianKernelIntersection_claim28515 : Prop :=
  ∀ {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A R : Subgroup (Equiv.Perm Ω))
    (blocks : Finset (Finset Ω)),
    binaryBlockSystem blocks →
    preservesBlocks A blocks →
    R ≤ A →
    regularAbelian R →
      Nat.card (kernelIntersection A R blocks) = 2 ∧
        regularOnEachBlock A R blocks ∧
        uniqueNonidentityFixedPointFree A R blocks

end

end MathlibPlus.Open.NewResearch2.R1052RegularAbelianKernel
