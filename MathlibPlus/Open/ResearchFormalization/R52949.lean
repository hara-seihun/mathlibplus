import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

def powerOrbit {Ω : Type*} (K : Subgroup (Equiv.Perm Ω))
    (n : ℕ) (x : Ω) : Set Ω :=
  {y | ∃ g : K, y = (g.1 ^ n) x}

def powerOrbitPartition {Ω : Type*} (K : Subgroup (Equiv.Perm Ω))
    (n : ℕ) : Set (Set Ω) :=
  {C | ∃ x : Ω, C = powerOrbit K n x}

def subgroupPartitionInvariant {Ω : Type*}
    (K : Subgroup (Equiv.Perm Ω)) (P : Set (Set Ω)) : Prop :=
  ∀ C, C ∈ P → ∀ g : K, Set.image g.1 C ∈ P

def subgroupSemiregular {Ω : Type*}
    (K : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ g : K, g ≠ 1 → ∀ x : Ω, g.1 x ≠ x

def regularOnSubgroup {Ω : Type*} [Fintype Ω]
    (K : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y : Ω, ∃! g : K, g.1 x = y

def centralizesSubgroups {Ω : Type*}
    (A E : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ a : A, ∀ e : E, a.1 * e.1 = e.1 * a.1

/-- R-4677, the divisibility lemma for an invariant C3-orbit partition. -/
def claim52949 : Prop :=
  ∀ (r : ℕ) (Ω : Type*) [Fintype Ω]
    (A B E : Subgroup (Equiv.Perm Ω)),
    regularOnSubgroup (A ⊔ E) →
    Nonempty (A ≃* Multiplicative (ZMod 9)) →
    Nonempty (B ≃* Multiplicative (ZMod 9)) →
    Nonempty (E ≃* Multiplicative (Fin r → ZMod 2)) →
    centralizesSubgroups A E →
    subgroupSemiregular B →
    ¬ 3 ∣ 2 ^ r →
    subgroupPartitionInvariant (A ⊔ E) (powerOrbitPartition B 3) →
    powerOrbitPartition B 3 = powerOrbitPartition A 3

end MathlibPlus.Open.ResearchFormalization
