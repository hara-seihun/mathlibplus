import Mathlib

namespace MathlibPlus.Open

/-- A finite collection of nonempty, pairwise disjoint subsets covering the carrier. -/
def finiteBlockSystem {Ω : Type*} (B : Finset (Set Ω)) : Prop :=
  (∀ U ∈ B, U.Nonempty) ∧
    (∀ ⦃U V : Set Ω⦄, U ∈ B → V ∈ B → U ≠ V → Disjoint U V) ∧
    (∀ x : Ω, ∃ U ∈ B, x ∈ U)

/-- The type of blocks in a finite block system. -/
abbrev blockType {Ω : Type*} (B : Finset (Set Ω)) :=
  {U : Set Ω // U ∈ B}

/-- Regularity of a subgroup of permutations of Ω. -/
def regularSubgroupOnOmega {Ω : Type*} {A : Subgroup (Equiv.Perm Ω)}
    (R : Subgroup A) : Prop :=
  ∀ x y : Ω, ∃! r : R, ((r.1 : A) : Equiv.Perm Ω) x = y

/-- Regularity of a subgroup of permutations of the block type. -/
def regularSubgroupOnBlocks {Ω : Type*} {B : Finset (Set Ω)}
    (S : Subgroup (Equiv.Perm (blockType B))) : Prop :=
  ∀ U V : blockType B, ∃! s : S, (s : Equiv.Perm (blockType B)) U = V

/-- Transitivity of a subgroup of permutations of Ω. -/
def transitiveSubgroupOnOmega {Ω : Type*} {A : Subgroup (Equiv.Perm Ω)}
    (R : Subgroup A) : Prop :=
  ∀ x y : Ω, ∃ r : R, ((r.1 : A) : Equiv.Perm Ω) x = y

/-- Transitivity of a subgroup of permutations of the block type. -/
def transitiveSubgroupOnBlocks {Ω : Type*} {B : Finset (Set Ω)}
    (S : Subgroup (Equiv.Perm (blockType B))) : Prop :=
  ∀ U V : blockType B, ∃ s : S, (s : Equiv.Perm (blockType B)) U = V

/-- The kernel action is regular on each block. -/
def kernelRegularOnEveryBlock {Ω : Type*} {B : Finset (Set Ω)}
    {A : Subgroup (Equiv.Perm Ω)}
    (π : A →* Equiv.Perm (blockType B)) : Prop :=
  ∀ U : blockType B,
    (∀ k : π.ker, ∀ x : Ω, x ∈ U.1 →
      ((k.1 : A) : Equiv.Perm Ω) x ∈ U.1) ∧
    (∀ x y : Ω, x ∈ U.1 → y ∈ U.1 →
      ∃! k : π.ker, ((k.1 : A) : Equiv.Perm Ω) x = y)

/-- Full preimage and image give the stated bijection of regular subgroups. -/
def fullPreimageRegularSubgroupBijection
    {Ω : Type*} [Fintype Ω]
    (B : Finset (Set Ω))
    (hB : finiteBlockSystem B)
    (A : Subgroup (Equiv.Perm Ω))
    (hA : ∀ a : A, ∀ U ∈ B, (a : Equiv.Perm Ω) '' U ∈ B)
    (hTrans : ∀ x y : Ω, ∃ a : A, (a : Equiv.Perm Ω) x = y)
    (π : A →* Equiv.Perm (blockType B))
    (hπ : ∀ (a : A) (U : blockType B),
      ((π a) U).1 = (a : Equiv.Perm Ω) '' U.1)
    (hK : kernelRegularOnEveryBlock π) : Prop :=
  (∀ S : Subgroup (Equiv.Perm (blockType B)),
      S ≤ π.range →
      regularSubgroupOnBlocks S →
      regularSubgroupOnOmega (S.comap π) ∧
        π.ker ≤ S.comap π ∧
        (S.comap π).map π = S) ∧
    (∀ R : Subgroup A,
      regularSubgroupOnOmega R →
      π.ker ≤ R →
      R.map π ≤ π.range ∧
        regularSubgroupOnBlocks (R.map π) ∧
        (R.map π).comap π = R)

/-- Cardinalities and transitivity of the full preimage of a regular quotient subgroup. -/
def preimageOfRegularQuotientSubgroupIsRegular
    {Ω : Type*} [Fintype Ω]
    (B : Finset (Set Ω))
    (hB : finiteBlockSystem B)
    (A : Subgroup (Equiv.Perm Ω))
    (hA : ∀ a : A, ∀ U ∈ B, (a : Equiv.Perm Ω) '' U ∈ B)
    (hTrans : ∀ x y : Ω, ∃ a : A, (a : Equiv.Perm Ω) x = y)
    (π : A →* Equiv.Perm (blockType B))
    (hπ : ∀ (a : A) (U : blockType B),
      ((π a) U).1 = (a : Equiv.Perm Ω) '' U.1)
    (hK : kernelRegularOnEveryBlock π)
    (b m : ℕ)
    (S : Subgroup (Equiv.Perm (blockType B))) : Prop :=
  (∀ U : blockType B,
      U.1.ncard = b) →
    Nat.card (blockType B) = m →
    S ≤ π.range →
    regularSubgroupOnBlocks S →
    Nat.card π.ker = b ∧
      Nat.card (S.comap π) = b * m ∧
      b * m = Nat.card Ω ∧
      transitiveSubgroupOnOmega (S.comap π) ∧
      regularSubgroupOnOmega (S.comap π)

/-- The image of a regular subgroup containing the kernel is regular on the blocks. -/
def imageOfRegularSubgroupContainingKernelIsRegular
    {Ω : Type*} [Fintype Ω]
    (B : Finset (Set Ω))
    (hB : finiteBlockSystem B)
    (A : Subgroup (Equiv.Perm Ω))
    (hA : ∀ a : A, ∀ U ∈ B, (a : Equiv.Perm Ω) '' U ∈ B)
    (hTrans : ∀ x y : Ω, ∃ a : A, (a : Equiv.Perm Ω) x = y)
    (π : A →* Equiv.Perm (blockType B))
    (hπ : ∀ (a : A) (U : blockType B),
      ((π a) U).1 = (a : Equiv.Perm Ω) '' U.1)
    (hK : kernelRegularOnEveryBlock π)
    (R : Subgroup A) : Prop :=
  regularSubgroupOnOmega R →
    π.ker ≤ R →
    R.map π ≤ π.range ∧
      Nat.card (R.map π) = Nat.card (blockType B) ∧
      transitiveSubgroupOnBlocks (R.map π) ∧
      regularSubgroupOnBlocks (R.map π) ∧
      Nat.card ((R.map π).comap π) = Nat.card R ∧
      R ≤ (R.map π).comap π ∧
      (R.map π).comap π = R

end MathlibPlus.Open
