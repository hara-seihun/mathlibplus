import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1052Claim28516

noncomputable section

open Classical
attribute [local instance] Classical.propDecidable Classical.decEq

private def binaryBlockSystem {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (blocks : Finset (Finset Ω)) : Prop :=
  (∀ B ∈ blocks, B.card = 2) ∧
    (∀ B ∈ blocks, ∀ C ∈ blocks, B = C ∨ Disjoint B C) ∧
    blocks.biUnion id = Finset.univ

private def preservesBlocks {Ω : Type*} [Fintype Ω]
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

private def canonicalDelta {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A : Subgroup (Equiv.Perm Ω))
    (blocks : Finset (Finset Ω)) (δ : Equiv.Perm Ω) : Prop :=
  δ ∈ A ∧ δ * δ = 1 ∧ (∀ x : Ω, δ x ≠ x) ∧
    (∀ B ∈ blocks, δ '' (B : Set Ω) = (B : Set Ω)) ∧
    (∀ a : A, (a : Equiv.Perm Ω) * δ = δ * (a : Equiv.Perm Ω))

private def kernelIntersectionIsDelta {Ω : Type*} [Fintype Ω]
    [DecidableEq Ω]
    (R : Subgroup (Equiv.Perm Ω))
    (K : Set (Equiv.Perm Ω)) (δ : Equiv.Perm Ω) : Prop :=
  δ ∈ R ∧ δ ∈ K ∧
    (∀ x : Equiv.Perm Ω, x ∈ R ∧ x ∈ K → x = 1 ∨ x = δ)

/-- Claim 28516: once the canonical global swap is fixed for the exact
finite invariant two-point block system, every regular abelian copy in the
same preserving group has the same literal kernel intersection. -/
def claim28516 : Prop :=
  ∀ {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A : Subgroup (Equiv.Perm Ω))
    (blocks : Finset (Finset Ω)) (m : ℕ),
    binaryBlockSystem blocks →
    blocks.card = m →
    preservesBlocks A blocks →
    (∃ R₀ : Subgroup (Equiv.Perm Ω),
      R₀ ≤ A ∧ regularAbelian R₀) →
    ∃ δ : Equiv.Perm Ω,
      canonicalDelta A blocks δ ∧
      ∀ R : Subgroup (Equiv.Perm Ω),
        R ≤ A →
        regularAbelian R →
        kernelIntersectionIsDelta R (blockKernel A blocks) δ

end

end MathlibPlus.Open.ResearchFormalization.R1052Claim28516
