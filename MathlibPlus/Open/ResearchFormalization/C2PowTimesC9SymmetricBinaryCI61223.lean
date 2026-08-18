import Mathlib
import MathlibPlus.Open.Cayley.C2PowTimesC9

namespace MathlibPlus.Open.ResearchFormalization.C2PowTimesC9SymmetricBinaryCI61223

noncomputable section

abbrev AddCarrier := MathlibPlus.Open.Cayley.C2PowTimesC9 2
abbrev H := Multiplicative AddCarrier

/-- Every relation in a finite labelled binary-relation tuple is symmetric. -/
def symmetricBinaryRelationTuple
    {Ω J : Type*} (E : J → Set (Ω × Ω)) : Prop :=
  ∀ j x y, (x, y) ∈ E j ↔ (y, x) ∈ E j

/-- A permutation preserves every labelled relation in a tuple. -/
def preservesBinaryRelationTuple
    {Ω J : Type*} (E : J → Set (Ω × Ω)) (σ : Equiv.Perm Ω) : Prop :=
  ∀ j x y, (x, y) ∈ E j ↔ (σ x, σ y) ∈ E j

/-- Regularity of a subgroup of the permutation group on its point carrier. -/
def regularPermutationSubgroup
    {Ω : Type*} (R : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃! r : R, (r : Equiv.Perm Ω) x = y

/-- A regular permutation subgroup is a regular copy of `C₂² × C₉`. -/
def regularHCopy
    {Ω : Type*} (R : Subgroup (Equiv.Perm Ω)) : Prop :=
  Nonempty (H ≃* R) ∧ regularPermutationSubgroup R

/-- Every element of a regular copy acts as an automorphism of every colour. -/
def relationsInvariantUnder
    {Ω J : Type*} (E : J → Set (Ω × Ω))
    (R : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ r : R, preservesBinaryRelationTuple E (r : Equiv.Perm Ω)

/-- Conjugacy inside the common colour-automorphism group. -/
def conjugatesPermutationSubgroups
    {Ω : Type*} (R T : Subgroup (Equiv.Perm Ω))
    (g : Equiv.Perm Ω) : Prop :=
  ∀ h : Equiv.Perm Ω,
    h ∈ R ↔ g * h * (g⁻¹) ∈ T

/-- Claim 61223: every finite tuple of symmetric binary relations preserved by
regular copies of `C₂² × C₉` has one conjugacy class of regular copies, with
the conjugator in the tuple's common automorphism group. -/
def claim61223_symmetricBinaryRelationalCI : Prop :=
  ∀ (Ω : Type*) [Fintype Ω],
    Fintype.card Ω = 36 →
      ∀ (J : Type*) [Finite J]
        (E : J → Set (Ω × Ω)),
        symmetricBinaryRelationTuple E →
          ∀ R T : Subgroup (Equiv.Perm Ω),
            regularHCopy R →
              relationsInvariantUnder E R →
                regularHCopy T →
                  relationsInvariantUnder E T →
                    ∃ g : Equiv.Perm Ω,
                      preservesBinaryRelationTuple E g ∧
                        conjugatesPermutationSubgroups R T g

end

end MathlibPlus.Open.ResearchFormalization.C2PowTimesC9SymmetricBinaryCI61223
