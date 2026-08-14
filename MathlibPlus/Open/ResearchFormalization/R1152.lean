import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1152

/-- The set of primes occurring in the order of an element of a finite group. -/
def hasOnlyPrimeFactorsIn {G : Type*} [Monoid G]
    (π : Set ℕ) (g : G) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ orderOf g → p ∈ π

def hasOnlyPrimeFactorsOutside {G : Type*} [Monoid G]
    (π : Set ℕ) (g : G) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ orderOf g → p ∉ π

def characteristicSubgroup {G : Type*} [Group G]
    (K : Subgroup G) : Prop :=
  ∀ φ : G ≃* G, φ '' (K : Set G) = K

def cayleyStep {G : Type*} [Group G]
    (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ ∃ s : G, s ∈ S ∧ x * s = y

def claim31604 : Prop :=
  ∀ (A H : Type*) [CommGroup A] [Fintype A] [Group H] [Fintype H],
    Nat.Coprime (Fintype.card A) (Fintype.card H) →
      let π : Set ℕ := {p : ℕ | Nat.Prime p ∧ p ∣ Fintype.card A}
      let AFactor : Subgroup (A × H) :=
        (⊤ : Subgroup A).prod (⊥ : Subgroup H)
      let HFactor : Subgroup (A × H) :=
        (⊥ : Subgroup A).prod (⊤ : Subgroup H)
      ((AFactor : Set (A × H)) =
          {x : A × H | hasOnlyPrimeFactorsIn π x}) ∧
      ((HFactor : Set (A × H)) =
          {x : A × H | hasOnlyPrimeFactorsOutside π x}) ∧
      characteristicSubgroup AFactor ∧
      characteristicSubgroup HFactor ∧
      (∀ z : A × H, z ∈ (AFactor : Set (A × H)) →
        ∀ g : A × H, z * g = g * z) ∧
      (∀ a : A, ∀ h : H, (a, h) = (a, 1) * (1, h)) ∧
      (∀ a a' : A, ∀ h h' : H,
        (a, 1) * (1, h) = (a', 1) * (1, h') → a = a' ∧ h = h')

/-- The same admitted characteristic Hall-factor statement under its second claim id. -/
def claim41367 : Prop :=
  ∀ (A H : Type*) [CommGroup A] [Fintype A] [Group H] [Fintype H],
    Nat.Coprime (Fintype.card A) (Fintype.card H) →
      let π : Set ℕ := {p : ℕ | Nat.Prime p ∧ p ∣ Fintype.card A}
      let AFactor : Subgroup (A × H) :=
        (⊤ : Subgroup A).prod (⊥ : Subgroup H)
      let HFactor : Subgroup (A × H) :=
        (⊥ : Subgroup A).prod (⊤ : Subgroup H)
      ((AFactor : Set (A × H)) =
          {x : A × H | hasOnlyPrimeFactorsIn π x}) ∧
      ((HFactor : Set (A × H)) =
          {x : A × H | hasOnlyPrimeFactorsOutside π x}) ∧
      characteristicSubgroup AFactor ∧
      characteristicSubgroup HFactor ∧
      (∀ z : A × H, z ∈ (AFactor : Set (A × H)) →
        ∀ g : A × H, z * g = g * z) ∧
      (∀ a : A, ∀ h : H, (a, h) = (a, 1) * (1, h)) ∧
      (∀ a a' : A, ∀ h h' : H,
        (a, 1) * (1, h) = (a', 1) * (1, h') → a = a' ∧ h = h')

def claim41373 : Prop :=
  ∀ (A H : Type*) [Group A] [Group H] [Fintype A] [Fintype H],
    Nontrivial A → Nontrivial H →
      let S : Set (A × H) :=
        ({1} : Set A) ×ˢ ((Set.univ : Set H) \ ({1} : Set H))
      let Adj : (A × H) → (A × H) → Prop := cayleyStep S
      (∀ s : A × H, s ∈ S → s⁻¹ ∈ S) ∧
      (∀ x y : A × H, Adj x y ↔ x.1 = y.1 ∧ x.2 ≠ y.2) ∧
      (∀ x y : A × H,
        Relation.ReflTransGen Adj x y ↔ x.1 = y.1) ∧
      (∀ a : A, ∀ x y : A × H,
        x.1 = a → y.1 = a → (Adj x y ↔ x ≠ y))

end MathlibPlus.Open.ResearchFormalization.R1152
