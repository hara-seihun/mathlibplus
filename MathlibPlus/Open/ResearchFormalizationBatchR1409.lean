import Mathlib

universe u v

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- A permutation preserves a finite tuple of binary relations when it preserves
all relations in both directions. -/
def preservesRelations
    (E : J → Ω → Ω → Prop) (σ : Equiv.Perm Ω) : Prop :=
  ∀ j x y, E j (σ x) (σ y) ↔ E j x y

/-- The symmetry condition for a finite tuple of binary relations. -/
def symmetricBinaryRelationalStructure
    (Ω : Type u) (J : Type v) [Fintype Ω] [Fintype J]
    (E : J → Ω → Ω → Prop) : Prop :=
  ∀ j x y, E j x y ↔ E j y x

/-- The permutations forming the automorphism group of the tuple. -/
def automorphismSet
    (Ω : Type u) (J : Type v) [Fintype Ω] [Fintype J]
    (E : J → Ω → Ω → Prop) : Set (Equiv.Perm Ω) :=
  {σ | preservesRelations E σ}

/-- A subgroup of a permutation group is regular on its underlying points. -/
def regularPermutationSubgroup
    (Ω : Type u) [Fintype Ω]
    (U : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃! u : U, u.1 x = y

/-- The exact order, cyclicity, and regularity package for a regular C₁₈. -/
def regularCyclic18
    (Ω : Type u) [Fintype Ω]
    (U : Subgroup (Equiv.Perm Ω)) : Prop :=
  Nat.card U = 18 ∧ IsCyclic U ∧ regularPermutationSubgroup Ω U

/-- Invariance of every relation under a permutation subgroup. -/
def relationsInvariantUnder
    (Ω : Type u) (J : Type v) [Fintype Ω] [Fintype J]
    (E : J → Ω → Ω → Prop)
    (U : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ u : U, ∀ j x y, E j (u.1 x) (u.1 y) ↔ E j x y

/-- C₁₈ is CI for every finite symmetric binary relational Cayley structure. -/
def c18SymmetricBinaryRelationalCI
    (Ω : Type u) (J : Type v) [Fintype Ω] [Fintype J]
    (E : J → Ω → Ω → Prop)
    (U : Subgroup (Equiv.Perm Ω)) : Prop :=
  Fintype.card Ω = 18 →
    symmetricBinaryRelationalStructure Ω J E →
    relationsInvariantUnder Ω J E U →
    regularCyclic18 Ω U →
    ∀ V : Subgroup (Equiv.Perm Ω),
      (regularCyclic18 Ω V ∧ ∀ v : V, v.1 ∈ automorphismSet Ω J E) →
      ∃ g : Equiv.Perm Ω,
        g ∈ automorphismSet Ω J E ∧
        ∀ v : Equiv.Perm Ω, v ∈ V ↔ g * v * (g⁻¹) ∈ U

/-- Membership in the unordered orbital of (x,y) for a permutation subgroup. -/
def sameUnorderedOrbital
    (Ω : Type u) [Fintype Ω]
    (H : Subgroup (Equiv.Perm Ω))
    (x y z w : Ω) : Prop :=
  ∃ h : H,
    (h.1 x = z ∧ h.1 y = w) ∨ (h.1 x = w ∧ h.1 y = z)

/-- The directed two-closure, expressed as preservation of every ordered
orbital. -/
def directedTwoClosureSet
    (Ω : Type u) [Fintype Ω]
    (A : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω) :=
  {σ | ∀ x y : Ω, ∃ a : A, a.1 x = σ x ∧ a.1 y = σ y}

/-- The permutations preserving every unordered H-orbital. -/
def unorderedOrbitalClosureSet
    (Ω : Type u) [Fintype Ω]
    (H : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω) :=
  {σ | ∀ x y : Ω, sameUnorderedOrbital Ω H x y (σ x) (σ y)}

/-- Symmetric H-invariant binary relations are unions of unordered H-orbitals,
and the permutations preserving those orbitals preserve the relations. -/
def symmetricRelationsAreUnorderedOrbitalUnions
    (Ω : Type u) (J : Type v) [Fintype Ω] [Fintype J]
    (A H : Subgroup (Equiv.Perm Ω))
    (E : J → Ω → Ω → Prop) : Prop :=
  (H : Set (Equiv.Perm Ω)) = directedTwoClosureSet Ω A →
    (∀ j x y, E j x y ↔ E j y x) →
    (∀ h : H, ∀ j x y, E j (h.1 x) (h.1 y) ↔ E j x y) →
    (∀ j, ∀ x y z w,
      sameUnorderedOrbital Ω H x y z w → (E j x y ↔ E j z w)) ∧
    (∀ σ : Equiv.Perm Ω,
      σ ∈ unorderedOrbitalClosureSet Ω H →
      σ ∈ automorphismSet Ω J E)

end MathlibPlus.Open.ResearchFormalizationBatch
