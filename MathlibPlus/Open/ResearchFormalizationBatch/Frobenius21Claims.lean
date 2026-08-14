import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch.Frobenius21Claims

open Classical

abbrev F5 := ZMod 5

def frobeniusSevenCycle : Equiv.Perm (Fin 7) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 *
    Equiv.swap 3 4 * Equiv.swap 4 5 * Equiv.swap 5 6

def frobeniusThreeCycle : Equiv.Perm (Fin 7) :=
  (Equiv.swap 1 2 * Equiv.swap 2 4) *
    (Equiv.swap 3 6 * Equiv.swap 6 5)

/-- A concrete permutation model of the Frobenius group `C₇ : C₃`. -/
def frobenius21 : Subgroup (Equiv.Perm (Fin 7)) :=
  Subgroup.closure
    ({frobeniusSevenCycle, frobeniusThreeCycle} : Set (Equiv.Perm (Fin 7)))

abbrev Frobenius21 := frobenius21

local instance : DecidableEq Frobenius21 := Classical.decEq _

def isSubgroupSet {G : Type} [Group G] (S : Set G) : Prop :=
  1 ∈ S ∧
    (∀ ⦃a b : G⦄, a ∈ S → b ∈ S → a * b ∈ S) ∧
    (∀ ⦃a : G⦄, a ∈ S → a⁻¹ ∈ S)

def isFibreTranslation (π : Equiv.Perm F5) : Prop :=
  ∃ c : F5, π = Equiv.addRight c

def nonlinearSupport
    (π : Frobenius21 → Equiv.Perm F5) : Set Frobenius21 :=
  {k | k ≠ 1 ∧ ¬ isFibreTranslation (π k)}

def leftTranslateSet {G : Type} [Group G] (g : G) (S : Set G) : Set G :=
  {x | ∃ y, y ∈ S ∧ x = g * y}

def leftStabilizerSet {G : Type} [Group G] (S : Set G) : Set G :=
  {g | leftTranslateSet g S = S}

/-- Claim 38441: the nonlinear-support left stabilizer is a subgroup. -/
def claim38441 : Prop :=
  ∀ (π : Frobenius21 → Equiv.Perm F5),
    π 1 = 1 → isSubgroupSet (leftStabilizerSet (nonlinearSupport π))

def subgroupCard {G : Type} [Group G] (K : Subgroup G) : Nat :=
  Nat.card K

def leftTranslateFinset {G : Type} [Group G] [DecidableEq G]
    (g : G) (S : Finset G) : Finset G :=
  S.image (fun y => g * y)

def subgroupInvariantFinset {G : Type} [Group G] [DecidableEq G]
    (K : Subgroup G) (S : Finset G) : Prop :=
  ∀ k : K, leftTranslateFinset (k : G) S = S

def leftCoset {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (K : Subgroup G) (g : G) : Finset G :=
  letI : Fintype K := Fintype.ofFinite K
  Finset.univ.filter (fun x => ∃ k : K, x = (k : G) * g)

def support21 (S : Finset Frobenius21) : Prop :=
  S.Nonempty ∧ 1 ∉ S

def supportStabilizerCard (S : Finset Frobenius21) : Nat :=
  Nat.card {g : Frobenius21 // leftTranslateFinset g S = S}

/--
Claim 38447: the concrete `C₇ : C₃` model has only the four stated subgroup
orders, with the stated subgroup and complement counts.
-/
def claim38447 : Prop :=
  letI : Fintype Frobenius21 := Fintype.ofFinite Frobenius21
  letI : Fintype (Subgroup Frobenius21) :=
    Fintype.ofFinite (Subgroup Frobenius21)
  (Nat.card Frobenius21 = 21) ∧
    (∀ K : Subgroup Frobenius21,
      subgroupCard K = 1 ∨ subgroupCard K = 3 ∨
        subgroupCard K = 7 ∨ subgroupCard K = 21) ∧
    Nat.card {K : Subgroup Frobenius21 // subgroupCard K = 1} = 1 ∧
    Nat.card {K : Subgroup Frobenius21 // subgroupCard K = 3} = 7 ∧
    Nat.card {K : Subgroup Frobenius21 // subgroupCard K = 7} = 1 ∧
    Nat.card {K : Subgroup Frobenius21 // subgroupCard K = 21} = 1 ∧
    (∃ N : Subgroup Frobenius21,
      subgroupCard N = 7 ∧ N.Normal ∧
        (∀ K : Subgroup Frobenius21, subgroupCard K = 3 →
          K ⊓ N = ⊥ ∧ K ⊔ N = ⊤) ∧
        (∀ N' : Subgroup Frobenius21,
          subgroupCard N' = 7 → N'.Normal → N' = N))

/--
Claim 38448: the exact histogram of nonempty supports in the nonidentity
points, together with its coset descriptions and the generation obstruction.
-/
def claim38448 : Prop :=
  letI : Fintype Frobenius21 := Fintype.ofFinite Frobenius21
  letI : Fintype (Subgroup Frobenius21) :=
    Fintype.ofFinite (Subgroup Frobenius21)
  let Supports := {S : Finset Frobenius21 // support21 S}
  (Nat.card Supports = 2 ^ 20 - 1) ∧
    (Nat.card {S : Supports // supportStabilizerCard S.1 = 1} = 1048131) ∧
    (Nat.card {S : Supports // supportStabilizerCard S.1 = 3} = 441) ∧
    (Nat.card {S : Supports // supportStabilizerCard S.1 = 7} = 3) ∧
    (∀ S : Supports,
      supportStabilizerCard S.1 = 1 ∨
        supportStabilizerCard S.1 = 3 ∨ supportStabilizerCard S.1 = 7) ∧
    (∀ K : Subgroup Frobenius21,
      subgroupCard K = 3 →
        Nat.card
            {C : Finset Frobenius21 //
              (∃ g : Frobenius21, C = leftCoset K g) ∧ 1 ∉ C} = 6 ∧
        Nat.card
            {S : Supports // subgroupInvariantFinset K S.1} = 2 ^ 6 - 1) ∧
    (∃! N : Subgroup Frobenius21,
      subgroupCard N = 7 ∧ N.Normal ∧
        Nat.card
            {S : Supports // subgroupInvariantFinset N S.1} = 2 ^ 2 - 1) ∧
    (∀ S : Supports, ∀ K₁ K₂ : Subgroup Frobenius21,
      K₁ ≠ ⊥ → K₂ ≠ ⊥ → K₁ ≠ K₂ →
        (∀ k : K₁, leftTranslateFinset (k : Frobenius21) S.1 = S.1) →
        (∀ k : K₂, leftTranslateFinset (k : Frobenius21) S.1 = S.1) →
        Subgroup.closure ((K₁ : Set Frobenius21) ∪ (K₂ : Set Frobenius21)) = ⊤ →
        False)

end MathlibPlus.Open.ResearchFormalizationBatch.Frobenius21Claims
