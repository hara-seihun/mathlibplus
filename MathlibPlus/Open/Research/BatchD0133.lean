import Mathlib

namespace MathlibPlus.Open.Research.BatchD0133

open Set

abbrev PermutationSubgroup (Ω : Type) := Subgroup (Equiv.Perm Ω)

def transitiveSubgroup {Ω : Type} (G : PermutationSubgroup Ω) : Prop :=
  ∀ x y : Ω, ∃ g : Equiv.Perm Ω, g ∈ G ∧ g x = y

def conjugatedMember {Ω : Type} (q : Equiv.Perm Ω)
    (H : PermutationSubgroup Ω) (g : Equiv.Perm Ω) : Prop :=
  ∃ h : Equiv.Perm Ω, h ∈ H ∧ g = q⁻¹ * h * q

def pointStabilizerOrbit {Ω : Type} (G : PermutationSubgroup Ω)
    (α x : Ω) : Set Ω :=
  {y | ∃ g : Equiv.Perm Ω, g ∈ G ∧ g α = α ∧ g x = y}

def twoClosure {Ω : Type} (G : PermutationSubgroup Ω) : Set (Equiv.Perm Ω) :=
  {q | ∀ x y : Ω, ∃ g : Equiv.Perm Ω, g ∈ G ∧ g x = q x ∧ g y = q y}

def ambientCertificate {Ω : Type} (G H : PermutationSubgroup Ω)
    (α : Ω) (q : Equiv.Perm Ω) : Prop :=
  q α = α ∧
    (∀ g : Equiv.Perm Ω, conjugatedMember q H g → g ∈ G) ∧
    (∀ x : Ω, q '' pointStabilizerOrbit G α x = pointStabilizerOrbit G α x)

def claim5805 (Ω : Type) (G H : PermutationSubgroup Ω)
    (α : Ω) (q : Equiv.Perm Ω) : Prop :=
  transitiveSubgroup G ∧ transitiveSubgroup H ∧ H ≤ G ∧
    ambientCertificate G H α q

def claim5806 : Prop :=
  ∀ {Ω : Type} (G H : PermutationSubgroup Ω) (α : Ω) (q : Equiv.Perm Ω),
    claim5805 Ω G H α q →
      ∀ x y : Ω, ∃ g : Equiv.Perm Ω,
        g ∈ G ∧ g x = q x ∧ g y = q y

def claim5807 : Prop :=
  ∀ {Ω : Type} (G H : PermutationSubgroup Ω) (α : Ω) (q : Equiv.Perm Ω),
    claim5805 Ω G H α q → q ∈ twoClosure G

def subgroupsConjugateWithin {Ω : Type}
    (K : Set (Equiv.Perm Ω)) (H : PermutationSubgroup Ω)
    (L : Equiv.Perm Ω → Prop) : Prop :=
  ∃ r : Equiv.Perm Ω, r ∈ K ∧
    ∀ g : Equiv.Perm Ω, L g ↔ conjugatedMember r H g

def claim5808 : Prop :=
  ∀ {Ω : Type} (G H : PermutationSubgroup Ω) (α : Ω) (q : Equiv.Perm Ω),
    claim5805 Ω G H α q →
      subgroupsConjugateWithin (twoClosure G) H (conjugatedMember q H)

def generatedAmbientGroup {Ω : Type} (H : PermutationSubgroup Ω)
    (q : Equiv.Perm Ω) : PermutationSubgroup Ω :=
  Subgroup.closure ((H : Set (Equiv.Perm Ω)) ∪ conjugatedMember q H)

def claim5809 : Prop :=
  (∀ {Ω : Type} (G H : PermutationSubgroup Ω) (α : Ω) (q : Equiv.Perm Ω),
    claim5805 Ω G H α q →
      subgroupsConjugateWithin (twoClosure G) H (conjugatedMember q H)) ∧
  (∀ {Ω : Type} (H : PermutationSubgroup Ω) (α : Ω) (q : Equiv.Perm Ω),
    let G := generatedAmbientGroup H q
    transitiveSubgroup G → transitiveSubgroup H → H ≤ G →
      claim5805 Ω G H α q →
        subgroupsConjugateWithin (twoClosure G) H (conjugatedMember q H))

end MathlibPlus.Open.Research.BatchD0133
