import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.PermutationClaims

def centralSubgroup {Ω : Type} (G D : Subgroup (Equiv.Perm Ω)) : Prop :=
  D ≤ G ∧ ∀ d, d ∈ D → ∀ g, g ∈ G → d * g = g * d

def semiregular {Ω : Type} (D : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ d, d ∈ D → d ≠ 1 → ∀ x : Ω, d x ≠ x

def isPartition {Ω I : Type} (U : I → Set Ω) : Prop :=
  (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧ (⋃ i, U i) = Set.univ

def isDInvariant {Ω I : Type} (D : Subgroup (Equiv.Perm Ω)) (U : I → Set Ω) : Prop :=
  ∀ i, ∀ d, d ∈ D → ∀ x, x ∈ U i → d x ∈ U i

def twoClosure {Ω : Type} (G : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω) :=
  {ψ | ∀ x y : Ω, ∃ h : G, (h : Equiv.Perm Ω) x = ψ x ∧ (h : Equiv.Perm Ω) y = ψ y}

def claim38406 : Prop :=
  ∀ {Ω : Type} (G D : Subgroup (Equiv.Perm Ω)) (I : Type)
    (U : I → Set Ω) (ψ : Equiv.Perm Ω) (g : I → G),
    centralSubgroup G D →
    semiregular D →
    isPartition U →
    isDInvariant D U →
    (∀ i x, x ∈ U i → ψ x = (g i : Equiv.Perm Ω) x) →
    (∀ x y : Ω,
      ∃ i j, x ∈ U i ∧ y ∈ U j ∧
        ∃ h : G,
          (h : Equiv.Perm Ω) x = (g i : Equiv.Perm Ω) x ∧
          (h : Equiv.Perm Ω) y = (g j : Equiv.Perm Ω) y) →
    ψ ∈ twoClosure G

end MathlibPlus.Open.ResearchFormalization.PermutationClaims
