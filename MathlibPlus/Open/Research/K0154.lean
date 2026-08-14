import Mathlib

namespace MathlibPlus.Open.Research.K0154

open scoped BigOperators

/-- The selected subsets represented by the primary Boolean variables. -/
def selectedSets (n : ℕ)
    (X : Finset (Fin n) → Bool) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun A => X A = true)

def familyFrequency {n : ℕ}
    (F : Finset (Finset (Fin n))) (i : Fin n) : ℕ :=
  (F.filter (fun A => i ∈ A)).card

/-- A distinct union-closed family on its actual labeled ground, with every
coordinate frequency strictly below half its family size. -/
def badFamily (n m : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  F.card = m ∧
    (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) ∧
    (∀ i : Fin n, ∃ A ∈ F, i ∈ A) ∧
    (∀ i : Fin n, 2 * familyFrequency F i ≤ m - 1)

/-- The ordinary exact-ground Boolean encoding. -/
def ordinaryEncodingSatisfies (n m : ℕ)
    (X : Finset (Fin n) → Bool) : Prop :=
  badFamily n m (selectedSets n X)

/-- The ordinary Boolean clauses decode exactly to the stated bad-family
conditions in the admitted parameter range. -/
def claim9664 : Prop :=
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → m ≤ 2 ^ n →
    ∀ X : Finset (Fin n) → Bool,
      ordinaryEncodingSatisfies n m X ↔
        (selectedSets n X).card = m ∧
          (∀ A ∈ selectedSets n X, ∀ B ∈ selectedSets n X,
            A ∪ B ∈ selectedSets n X) ∧
          (∀ i : Fin n, ∃ A ∈ selectedSets n X, i ∈ A) ∧
          (∀ i : Fin n,
            2 * familyFrequency (selectedSets n X) i ≤ m - 1)

/-- Exact model/family correspondence, including the unique primary assignment
for a decoded family. -/
def claim9665 : Prop :=
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → m ≤ 2 ^ n →
    (∀ X : Finset (Fin n) → Bool,
        ordinaryEncodingSatisfies n m X ↔
          badFamily n m (selectedSets n X)) ∧
    (∀ F : Finset (Finset (Fin n)), badFamily n m F →
      ∃! X : Finset (Fin n) → Bool, selectedSets n X = F)

/-- The five additional minimum-counterexample conditions. -/
def minimumForm (n m : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  badFamily n m F ∧
    ∅ ∈ F ∧
    3 ≤ m ∧ Odd m ∧
    3 ≤ n ∧
    (∀ i : Fin n, ∃ A ∈ F, i ∉ A ∧ A ∪ ({i} : Finset (Fin n)) ∈ F) ∧
    (∃ i j k : Fin n,
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      familyFrequency F i = (m - 1) / 2 ∧
      familyFrequency F j = (m - 1) / 2 ∧
      familyFrequency F k = (m - 1) / 2)

/-- The minimum-form encoding is the ordinary encoding plus `minimumForm`. -/
def minimumEncodingSatisfies (n m : ℕ)
    (X : Finset (Fin n) → Bool) : Prop :=
  ordinaryEncodingSatisfies n m X ∧
    minimumForm n m (selectedSets n X)

/-- No exact-ground-size-five family has all five coordinate frequencies below
half its size. -/
def claim9672 : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ 32 → ¬ ∃ F : Finset (Finset (Fin 5)), badFamily 5 m F

/-- The minimum-form encoding has no model on a five-coordinate ground for any
admissible odd family size. -/
def claim9673 : Prop :=
  ∀ m : ℕ, 3 ≤ m → m ≤ 31 → Odd m →
    ¬ ∃ X : Finset (Fin 5) → Bool,
      minimumEncodingSatisfies 5 m X

end MathlibPlus.Open.Research.K0154
