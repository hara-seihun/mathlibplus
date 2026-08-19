import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1155Claim41411

noncomputable section

abbrev Q8 := QuaternionGroup 2
abbrev BinaryC2 := Multiplicative (ZMod 2)
abbrev QuotientGroup (A : Type*) := A × (BinaryC2 × BinaryC2)
abbrev FullGroup (A : Type*) := A × Q8

def relationAutomorphismSet {Ω : Type*}
    (Γ : Ω → Ω → Prop) : Set (Equiv.Perm Ω) :=
  {a | ∀ x y, Γ (a x) (a y) ↔ Γ x y}

def actualInducedBlockAction
    {Ω β : Type*} (q : Ω → β)
    (Y : Set (Equiv.Perm Ω)) : Set (Equiv.Perm β) :=
  {a | ∃ y, y ∈ Y ∧ ∀ x : Ω, a (q x) = q (y x)}

def quotientCopyImage
    {Ω β : Type*} (q : Ω → β)
    (R : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm β) :=
  {a | ∃ r, r ∈ R ∧ ∀ x : Ω, a (q x) = q (r x)}

def regularCopy {G Ω : Type*} [Group G]
    (R : Subgroup (Equiv.Perm Ω)) : Prop :=
  (∀ x y : Ω, ∃! r : R, (r : Equiv.Perm Ω) x = y) ∧
    Nonempty (R ≃* G)

def conjugateWithin
    {Ω : Type*} (Y : Set (Equiv.Perm Ω))
    (R T : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∃ a, a ∈ Y ∧
    ∀ r : Equiv.Perm Ω, r ∈ R ↔ a * r * a⁻¹ ∈ T

def quotientConjugateWithin
    {β : Type*} (Y : Set (Equiv.Perm β))
    (R T : Set (Equiv.Perm β)) : Prop :=
  ∃ a, a ∈ Y ∧
    ∀ r : Equiv.Perm β, r ∈ R ↔ a * r * a⁻¹ ∈ T

def commonTwoPointBlockSystem
    {Ω β : Type*} [Fintype Ω]
    (q : Ω → β) : Prop :=
  Function.Surjective q ∧
    ∀ b : β, Set.ncard {x : Ω | q x = b} = 2

def preservesCommonBlockSystem
    {Ω β : Type*} (q : Ω → β)
    (Y : Set (Equiv.Perm Ω)) : Prop :=
  ∀ y : Equiv.Perm Ω, y ∈ Y →
    ∃ a : Equiv.Perm β, ∀ x : Ω, a (q x) = q (y x)

def quotientCopyAgreement
    {Ω β : Type*} (q : Ω → β)
    (R : Subgroup (Equiv.Perm Ω))
    (RQ : Subgroup (Equiv.Perm β)) : Prop :=
  ∀ a : Equiv.Perm β,
    a ∈ RQ ↔ a ∈ quotientCopyImage q R

/-- Claim 41411: for a fixed graph or digraph whose full automorphism set
preserves the common two-point block quotient, conjugacy of regular
`A × Q₈` copies is equivalent to conjugacy of their actual induced
`A × C₂²` quotient copies inside the actual induced block action. -/
def claim41411 : Prop :=
  ∀ (A Ω β : Type*) [CommGroup A] [Fintype A]
    [Fintype Ω] [DecidableEq Ω] [Fintype β] [DecidableEq β],
    Odd (Fintype.card A) →
      ∀ (Γ : Ω → Ω → Prop)
        (q : Ω → β)
        (R T : Subgroup (Equiv.Perm Ω))
        (RQ TQ : Subgroup (Equiv.Perm β)),
        let Y := relationAutomorphismSet Γ
        commonTwoPointBlockSystem q →
          preservesCommonBlockSystem q Y →
          R ≤ (Y : Set (Equiv.Perm Ω)) →
          T ≤ (Y : Set (Equiv.Perm Ω)) →
          regularCopy (G := FullGroup A) R →
          regularCopy (G := FullGroup A) T →
          regularCopy (G := QuotientGroup A) RQ →
          regularCopy (G := QuotientGroup A) TQ →
          quotientCopyAgreement q R RQ →
          quotientCopyAgreement q T TQ →
            (conjugateWithin Y R T ↔
              quotientConjugateWithin
                (actualInducedBlockAction q Y)
                (RQ : Set (Equiv.Perm β))
                (TQ : Set (Equiv.Perm β)))

end
end MathlibPlus.Open.ResearchFormalization.R1155Claim41411
