import MathlibPlus.Open.NewResearch2.R1052SharedCentralInvolution

namespace MathlibPlus.Open.ResearchFormalization.Claim28517GlobalSwapCentral

noncomputable section

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
  (∀ x y : R,
    (x : Equiv.Perm Ω) * (y : Equiv.Perm Ω) =
      (y : Equiv.Perm Ω) * (x : Equiv.Perm Ω)) ∧
    (∀ x y : Ω, ∃! r : R, (r : Equiv.Perm Ω) x = y)

private def blockKernel {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A : Subgroup (Equiv.Perm Ω))
    (blocks : Finset (Finset Ω)) : Set (Equiv.Perm Ω) :=
  {a | a ∈ A ∧ ∀ B ∈ blocks,
    a '' (B : Set Ω) = (B : Set Ω)}

private def globalSwapData {Ω : Type*} [Fintype Ω]
    (blocks : Finset (Finset Ω)) (δ : Equiv.Perm Ω) : Prop :=
  δ * δ = 1 ∧
    (∀ x : Ω, δ x ≠ x) ∧
    (∀ B ∈ blocks, δ '' (B : Set Ω) = (B : Set Ω))

private def kernelIntersectionIsDelta {Ω : Type*} [Fintype Ω]
    (R : Subgroup (Equiv.Perm Ω))
    (K : Set (Equiv.Perm Ω)) (δ : Equiv.Perm Ω) : Prop :=
  δ ∈ R ∧ δ ∈ K ∧
    (∀ x : Equiv.Perm Ω,
      x ∈ R ∧ x ∈ K → x = 1 ∨ x = δ)

private def setwiseStabilizer {Ω : Type*}
    (blocks : Finset (Finset Ω)) : Set (Equiv.Perm Ω) :=
  {g | ∀ B ∈ blocks,
    ∃ C ∈ blocks, Set.image g (B : Set Ω) = (C : Set Ω)}

/-- Claim 28517: the all-block global swap is central in the full setwise
stabilizer of the binary block system, and therefore belongs to the center of
any supplied block-preserving subgroup `A`; `A` is not identified with that
full stabilizer. -/
def claim28517 : Prop :=
  ∀ {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A R : Subgroup (Equiv.Perm Ω))
    (blocks : Finset (Finset Ω)) (δ : Equiv.Perm Ω),
    binaryBlockSystem blocks →
    preservesBlocks A blocks →
    R ≤ A →
    regularAbelian R →
    globalSwapData blocks δ →
    kernelIntersectionIsDelta R (blockKernel A blocks) δ →
      (∀ g : Equiv.Perm Ω,
        g ∈ setwiseStabilizer blocks → g * δ = δ * g) ∧
      δ ∈ A ∧
        (∀ a : A,
          (a : Equiv.Perm Ω) * δ = δ * (a : Equiv.Perm Ω))

end

end MathlibPlus.Open.ResearchFormalization.Claim28517GlobalSwapCentral
