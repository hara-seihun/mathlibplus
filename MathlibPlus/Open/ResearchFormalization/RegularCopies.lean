import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.RegularCopies


def regularCopy
    (H Ω : Type*) [Group H] [Fintype H] [Fintype Ω]
    (R : Subgroup (Equiv.Perm Ω)) (e : H ≃* R) : Prop :=
  ∀ x y : Ω, ∃! h : H, ((e h : R) : Equiv.Perm Ω) x = y


def characteristicSubgroup (H : Type*) [Group H] (K : Subgroup H) : Prop :=
  ∀ φ : H ≃* H, ∀ x : H, x ∈ K ↔ φ x ∈ K


def characteristicOrbit
    (H Ω : Type*) [Group H]
    (K : Subgroup H) (R : Subgroup (Equiv.Perm Ω))
    (e : H ≃* R) (x : Ω) : Set Ω :=
  {y | ∃ k : K, ((e (k : H) : R) : Equiv.Perm Ω) x = y}


def orbitPartition
    (H Ω : Type*) [Group H]
    (K : Subgroup H) (R : Subgroup (Equiv.Perm Ω))
    (e : H ≃* R) : Set (Set Ω) :=
  Set.range (characteristicOrbit H Ω K R e)


def conjugatesBy
    (Ω : Type*) [Fintype Ω]
    (f : Equiv.Perm Ω)
    (R T : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ p : Equiv.Perm Ω,
    p ∈ T ↔ ∃ r : Equiv.Perm Ω, r ∈ R ∧ p = f⁻¹ * r * f


def setwiseStabilizes
    (Ω : Type*) (f : Equiv.Perm Ω) (B : Set (Set Ω)) : Prop :=
  ∀ C : Set Ω, C ∈ B → Set.image f C ∈ B


def claim35710
    (H Ω : Type*) [Group H] [Fintype H] [Fintype Ω]
    (K : Subgroup H)
    (R T : Subgroup (Equiv.Perm Ω))
    (eR : H ≃* R) (eT : H ≃* T)
    (f : Equiv.Perm Ω) : Prop :=
  characteristicSubgroup H K →
    regularCopy H Ω R eR →
      regularCopy H Ω T eT →
        orbitPartition H Ω K R eR = orbitPartition H Ω K T eT →
          conjugatesBy Ω f R T →
            setwiseStabilizes Ω f (orbitPartition H Ω K R eR)

end MathlibPlus.Open.ResearchFormalization.RegularCopies
