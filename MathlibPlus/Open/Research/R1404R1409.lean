import Mathlib

namespace MathlibPlus.Open.Research.R1404R1409

noncomputable section

abbrev ScalarSwitchDomain := Fin 2 → ZMod 3

def normalizedScalarSwitch (g : ScalarSwitchDomain → ZMod 3) : Prop :=
  g 0 = 0

abbrev NormalizedScalarSwitch :=
  {g : ScalarSwitchDomain → ZMod 3 // normalizedScalarSwitch g}

abbrev NormalizedAtlasRow := Fin 9 × NormalizedScalarSwitch

def claim38676_normalizedScalarSwitchAtlas : Prop :=
  Nat.card NormalizedScalarSwitch = 6561 ∧
    Nat.card NormalizedAtlasRow = 59049 ∧
    (3 : ℕ) ^ 8 = 6561 ∧
    9 * 6561 = 59049

def generatedOrbital {α : Type*}
    (A : Subgroup (Equiv.Perm α))
    (p q : α × α) : Prop :=
  ∃ a : A, q.1 = a.1 p.1 ∧ q.2 = a.1 p.2

def twoClosureMember {α : Type*}
    (A : Subgroup (Equiv.Perm α)) (g : Equiv.Perm α) : Prop :=
  ∀ x y : α, ∃ a : A, g x = a.1 x ∧ g y = a.1 y

def generatorInvariant {α ι : Type*}
    (U V : Set (Equiv.Perm α)) (R : ι → α → α → Prop) : Prop :=
  (∀ u ∈ U, ∀ i x y, R i (u x) (u y) ↔ R i x y) ∧
    (∀ v ∈ V, ∀ i x y, R i (v x) (v y) ↔ R i x y)

def claim38732_generatedOrbitalRelationPreservation : Prop :=
  ∀ {α ι : Type*} (U V : Set (Equiv.Perm α))
    (R : ι → α → α → Prop),
    generatorInvariant U V R →
    let A := Subgroup.closure (U ∪ V)
    (∀ i : ι, ∀ p q : α × α,
      generatedOrbital A p q →
        (R i p.1 p.2 ↔ R i q.1 q.2)) ∧
    (∀ g : Equiv.Perm α, twoClosureMember A g →
      ∀ i x y, R i (g x) (g y) ↔ R i x y)

end

end MathlibPlus.Open.Research.R1404R1409
