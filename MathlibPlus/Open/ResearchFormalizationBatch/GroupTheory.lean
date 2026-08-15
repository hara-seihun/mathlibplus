import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

abbrev BooleanQuotient (A : Type*) := A × (ZMod 2 × ZMod 2)


def dedekindAndSplit31616 (A : Type*) [Fintype A] [CommGroup A]
    (_hodd : Odd (Fintype.card A)) : Prop :=
  (∀ U : Subgroup (QuaternionGroup 2), U.Normal) ∧
    (∀ S : Subgroup (A × QuaternionGroup 2), S.Normal) ∧
    (∀ S : Subgroup (A × QuaternionGroup 2),
      ∃! CU : Subgroup A × Subgroup (QuaternionGroup 2),
        S = Subgroup.prod CU.1 CU.2)


def dedekindAndSplit41379 (A : Type*) [Fintype A] [CommGroup A]
    (_hodd : Odd (Fintype.card A)) : Prop :=
  (∀ U : Subgroup (QuaternionGroup 2), U.Normal) ∧
    (∀ S : Subgroup (A × QuaternionGroup 2), S.Normal) ∧
    (∀ S : Subgroup (A × QuaternionGroup 2),
      ∃! CU : Subgroup A × Subgroup (QuaternionGroup 2),
        S = Subgroup.prod CU.1 CU.2)


def linearitySet31633 {A : Type*} [AddCommGroup A]
    (b : BooleanQuotient A → ZMod 2) : Set (BooleanQuotient A) :=
  {h | ∀ u, b (h + u) = b h + b u}


def linearitySubgroupAndCharacterExtension31633
    (A : Type*) [Fintype A] [AddCommGroup A]
    (_hodd : Odd (Fintype.card A))
    (b : BooleanQuotient A → ZMod 2) (_hb : b 0 = 0) : Prop :=
  ∃ L : AddSubgroup (BooleanQuotient A),
    (∀ h, h ∈ L ↔ h ∈ linearitySet31633 b) ∧
    (∃ φ : L →+ ZMod 2, ∀ h : L, φ h = b h) ∧
    (∃ χ : BooleanQuotient A →+ ZMod 2, ∀ h : L, χ h = b h)


def linearitySet41396 {A : Type*} [AddCommGroup A]
    (b : BooleanQuotient A → ZMod 2) : Set (BooleanQuotient A) :=
  {h | ∀ u, b (h + u) = b h + b u}


def linearitySubgroupAndCharacterExtension41396
    (A : Type*) [Fintype A] [AddCommGroup A]
    (_hodd : Odd (Fintype.card A))
    (b : BooleanQuotient A → ZMod 2) (_hb : b 0 = 0) : Prop :=
  ∃ L : AddSubgroup (BooleanQuotient A),
    (∀ h, h ∈ L ↔ h ∈ linearitySet41396 b) ∧
    (∃ φ : L →+ ZMod 2, ∀ h : L, φ h = b h) ∧
    (∃ χ : BooleanQuotient A →+ ZMod 2, ∀ h : L, χ h = b h)

end MathlibPlus.Open.ResearchFormalizationBatch
