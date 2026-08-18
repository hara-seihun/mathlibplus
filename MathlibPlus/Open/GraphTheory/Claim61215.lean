import Mathlib

universe u v

namespace MathlibPlus.Open.GraphTheory.Claim61215

/-- A permutation preserves every labelled binary relation in a tuple. -/
def preservesBinaryRelationTuple
    {Ω : Type u} {J : Type v}
    (E : J → Set (Ω × Ω)) (σ : Equiv.Perm Ω) : Prop :=
  ∀ j x y, (x, y) ∈ E j ↔ (σ x, σ y) ∈ E j

/-- Every relation in a labelled binary-relation tuple is symmetric. -/
def symmetricBinaryRelationTuple
    {Ω : Type u} {J : Type v}
    (E : J → Set (Ω × Ω)) : Prop :=
  ∀ j x y, (x, y) ∈ E j ↔ (y, x) ∈ E j

/-- Regularity of a permutation subgroup on its point carrier. -/
def regularPermutationSubgroup
    {Ω : Type u} (R : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃! r : R, r.1 x = y

/-- A regular permutation subgroup is a regular copy of the displayed group. -/
def isRegularCopy
    {G : Type u} {Ω : Type v} [Group G]
    (R : Subgroup (Equiv.Perm Ω)) : Prop :=
  Nonempty (G ≃* R) ∧ regularPermutationSubgroup R

/-- A permutation subgroup leaves every labelled relation invariant. -/
def relationsInvariantUnder
    {Ω : Type u} {J : Type v}
    (E : J → Set (Ω × Ω)) (R : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ r : R, preservesBinaryRelationTuple E r.1

/-- Conjugacy of two permutation subgroups by a specified permutation. -/
def conjugatesPermutationSubgroups
    {Ω : Type u}
    (R T : Subgroup (Equiv.Perm Ω)) (g : Equiv.Perm Ω) : Prop :=
  ∀ h : Equiv.Perm Ω, h ∈ R ↔ g * h * (g⁻¹) ∈ T

/-- Symmetric binary-relational CI for a finite group: every finite tuple of
symmetric binary relations invariant under a regular copy has one conjugacy
class of regular copies of the group inside its colour automorphism group. -/
def symmetricBinaryRelationalCI
    (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (J : Type) [Finite J]
    (E : J → Set (G × G))
    (R : Subgroup (Equiv.Perm G)),
    symmetricBinaryRelationTuple E →
    isRegularCopy (G := G) R →
    relationsInvariantUnder E R →
    ∀ T : Subgroup (Equiv.Perm G),
      isRegularCopy (G := G) T →
      relationsInvariantUnder E T →
      ∃ g : Equiv.Perm G,
        preservesBinaryRelationTuple E g ∧
        conjugatesPermutationSubgroups R T g

/-- Claim 61215: symmetric binary-relational CI passes from a direct product
with the complement C₂ to its direct factor. -/
def claim61215_symmetricBinaryRelationalCI_directFactorC2 : Prop :=
  ∀ (K : Type u) [Group K] [Finite K],
    symmetricBinaryRelationalCI (K × Multiplicative (ZMod 2)) →
      symmetricBinaryRelationalCI K

end MathlibPlus.Open.GraphTheory.Claim61215
