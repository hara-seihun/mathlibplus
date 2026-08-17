import Mathlib

namespace MathlibPlus.Open.NewResearch2.R1052SharedCentralInvolution

noncomputable section

open Classical
attribute [local instance] Classical.propDecidable Classical.decEq

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

private def quotientClass {Ω : Type*} [Fintype Ω]
    (R : Subgroup (Equiv.Perm Ω)) (δ r : Equiv.Perm Ω) :
    Set (Equiv.Perm Ω) :=
  {s | s ∈ R ∧ (s = r ∨ s = r * δ)}

private def quotientClasses {Ω : Type*} [Fintype Ω]
    (R : Subgroup (Equiv.Perm Ω)) (δ : Equiv.Perm Ω) :
    Set (Set (Equiv.Perm Ω)) :=
  {Q | ∃ r : Equiv.Perm Ω, r ∈ R ∧ Q = quotientClass R δ r}

private def quotientRegularOnBlocks {Ω : Type*} [Fintype Ω]
    [DecidableEq Ω]
    (R : Subgroup (Equiv.Perm Ω))
    (blocks : Finset (Finset Ω)) (δ : Equiv.Perm Ω) : Prop :=
  ∀ B ∈ blocks, ∀ C ∈ blocks, ∃! Q : Set (Equiv.Perm Ω),
    Q ∈ quotientClasses R δ ∧
      ∃ r : Equiv.Perm Ω, r ∈ Q ∧ r ∈ R ∧
        r '' (B : Set Ω) = (C : Set Ω)

private def sharedSetup {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A R : Subgroup (Equiv.Perm Ω))
    (blocks : Finset (Finset Ω)) (δ : Equiv.Perm Ω) : Prop :=
  binaryBlockSystem blocks ∧
    preservesBlocks A blocks ∧
    R ≤ A ∧ regularAbelian R ∧
    canonicalDelta A blocks δ ∧
    kernelIntersectionIsDelta R (blockKernel A blocks) δ

/-- Claim 28518: once the exact shared binary-block kernel and literal delta
intersection are in place, R/<delta> acts regularly on the actual block set. -/
def claim28518 : Prop :=
  ∀ {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A R : Subgroup (Equiv.Perm Ω))
    (blocks : Finset (Finset Ω)) (δ : Equiv.Perm Ω),
    sharedSetup A R blocks δ →
      quotientRegularOnBlocks R blocks δ

/-- Claim 28519: every finite permutation group with an invariant two-point
block system and regular abelian subgroup has a canonical central global swap,
shared literal kernel intersection, and quotient regularity on blocks. -/
def claim28519 : Prop :=
  ∀ {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A R : Subgroup (Equiv.Perm Ω))
    (blocks : Finset (Finset Ω)),
    binaryBlockSystem blocks →
    preservesBlocks A blocks →
    R ≤ A →
    regularAbelian R →
      ∃ δ : Equiv.Perm Ω,
        sharedSetup A R blocks δ ∧
        (∀ ε : Equiv.Perm Ω,
          canonicalDelta A blocks ε → ε = δ) ∧
        quotientRegularOnBlocks R blocks δ

end

end MathlibPlus.Open.NewResearch2.R1052SharedCentralInvolution
