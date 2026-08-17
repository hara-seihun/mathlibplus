import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1404

noncomputable section

abbrev BasePoint := Fin 2 → ZMod 3
abbrev AtlasPoint := ZMod 3 × BasePoint
abbrev BasePermutation := Equiv.Perm BasePoint
abbrev AtlasPermutation := Equiv.Perm AtlasPoint

/-- The regular translation copy on the base plane. -/
def baseTranslationSubgroup : Subgroup BasePermutation :=
  Subgroup.closure (Set.range (fun b : BasePoint => Equiv.addRight b))

/-- The base holomorph, used to form ordered double-coset positions. -/
def baseHolomorph : Subgroup BasePermutation :=
  Subgroup.normalizer (baseTranslationSubgroup : Set BasePermutation)

def baseDoubleCosetStep (ρ τ : BasePermutation) : Prop :=
  ∃ a b : baseHolomorph,
    τ = (a : BasePermutation) * ρ * (b : BasePermutation)

def basePositionSetoid : Setoid BasePermutation where
  r := Relation.EqvGen baseDoubleCosetStep
  iseqv := {
    refl := fun ρ => Relation.EqvGen.refl ρ
    symm := fun {ρ τ} h => Relation.EqvGen.symm ρ τ h
    trans := fun {ρ τ υ} h₁ h₂ => Relation.EqvGen.trans ρ τ υ h₁ h₂ }

abbrev BasePosition := Quotient basePositionSetoid

noncomputable def positionRepresentative (p : BasePosition) : BasePermutation :=
  Quotient.out p

/-- The lift of a base permutation to the second coordinate of the atlas. -/
def liftBase (ρ : BasePermutation) : AtlasPermutation :=
  Equiv.prodCongr (Equiv.refl (ZMod 3)) ρ

/-- The normalized scalar carry switch. -/
def carrySwitch (g : BasePoint → ZMod 3) : AtlasPermutation :=
  { toFun := fun p => (p.1 + g p.2, p.2)
    invFun := fun p => (p.1 - g p.2, p.2)
    left_inv := by
      rintro ⟨c, v⟩
      simp [sub_eq_add_neg, add_assoc]
    right_inv := by
      rintro ⟨c, v⟩
      simp [sub_eq_add_neg, add_assoc] }

def normalizedCarry (g : BasePoint → ZMod 3) : Prop :=
  g 0 = 0

/-- The defining carry transporter and the first regular `C₃³` copy. -/
def definingTransporter (ρ : BasePermutation)
    (g : BasePoint → ZMod 3) : AtlasPermutation :=
  liftBase ρ * carrySwitch g

def regularAtlasSubgroup : Subgroup AtlasPermutation :=
  Subgroup.closure (Set.range (fun x : AtlasPoint => Equiv.addRight x))

def conjugatedSubgroup {α : Type*} (F : Equiv.Perm α)
    (R : Subgroup (Equiv.Perm α)) : Subgroup (Equiv.Perm α) :=
  Subgroup.map (MulAut.conj F).toMonoidHom R

def secondRegularCopy (p : BasePosition)
    (g : BasePoint → ZMod 3) : Subgroup AtlasPermutation :=
  conjugatedSubgroup (definingTransporter (positionRepresentative p) g)
    regularAtlasSubgroup

def generatedPair (p : BasePosition)
    (g : BasePoint → ZMod 3) : Subgroup AtlasPermutation :=
  regularAtlasSubgroup ⊔ secondRegularCopy p g

/-- The directed binary two-closure of a permutation subgroup. -/
def directedBinaryTwoClosure
    (X : Subgroup AtlasPermutation) : Set AtlasPermutation :=
  {F | ∀ a b : AtlasPoint, ∃ x : AtlasPermutation,
    x ∈ X ∧ x a = F a ∧ x b = F b}

def regularPermutationSubgroup
    (R : Subgroup AtlasPermutation) : Prop :=
  ∀ x y : AtlasPoint, ∃! r : R, (r : AtlasPermutation) x = y

def conjugateInGeneratedTwoClosure (p : BasePosition)
    (g : BasePoint → ZMod 3) : Prop :=
  ∃ h : AtlasPermutation,
    h ∈ directedBinaryTwoClosure (generatedPair p g) ∧
      conjugatedSubgroup h regularAtlasSubgroup = secondRegularCopy p g

def definingTransporterInClosure (p : BasePosition)
    (g : BasePoint → ZMod 3) : Prop :=
  definingTransporter (positionRepresentative p) g ∈
    directedBinaryTwoClosure (generatedPair p g)

def fixesAtlasOrigin (h : AtlasPermutation) : Prop :=
  h 0 = 0

def alternateOriginFixingConjugator (p : BasePosition)
    (g : BasePoint → ZMod 3) : Prop :=
  ∃ h : AtlasPermutation,
    h ∈ directedBinaryTwoClosure (generatedPair p g) ∧
      fixesAtlasOrigin h ∧
      conjugatedSubgroup h regularAtlasSubgroup = secondRegularCopy p g

def atlasFailureRows :=
  {row : BasePosition × (BasePoint → ZMod 3) //
    normalizedCarry row.2 ∧ ¬ definingTransporterInClosure row.1 row.2}

/-- Claim 38681: every position and normalized carry gives two regular copies
that are conjugate in the generated directed binary two-closure. -/
def claim38681 : Prop :=
  Nat.card BasePosition = 9 ∧
    Nat.card {g : BasePoint → ZMod 3 // normalizedCarry g} = 6561 ∧
    (regularPermutationSubgroup regularAtlasSubgroup) ∧
    ∀ p : BasePosition, ∀ g : BasePoint → ZMod 3,
      normalizedCarry g →
        regularPermutationSubgroup (secondRegularCopy p g) ∧
          conjugateInGeneratedTwoClosure p g

/-- Claim 38682: the defining transporter misses in exactly 572 rows, but
those misses all have an origin-fixing conjugator in the same two-closure. -/
def claim38682 : Prop :=
  ¬ (∀ p : BasePosition, ∀ g : BasePoint → ZMod 3,
      normalizedCarry g →
        ¬ definingTransporterInClosure p g →
          ¬ conjugateInGeneratedTwoClosure p g) ∧
    Nat.card atlasFailureRows = 572 ∧
    ∀ p : BasePosition, ∀ g : BasePoint → ZMod 3,
      normalizedCarry g →
        ¬ definingTransporterInClosure p g →
          alternateOriginFixingConjugator p g

end

end MathlibPlus.Open.ResearchFormalization.R1404
