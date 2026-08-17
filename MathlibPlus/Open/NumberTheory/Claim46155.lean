import Mathlib

noncomputable section
open Classical
open scoped BigOperators

namespace MathlibPlus.Open.NumberTheory

abbrev PositiveIndex := {n : ℕ // 0 < n}
abbrev BinaryWord := ℕ → Fin 2
abbrev ChoiceSequence := ℕ → Fin 2

def dyadicWeight (a : PositiveIndex) : ℚ :=
  (a.1 : ℚ) / (2 : ℚ) ^ a.1

def subsetRepresentation (x : ℚ) (A : Set PositiveIndex) : Prop :=
  (∑' a : PositiveIndex, if a ∈ A then dyadicWeight a else 0) = x

def balancedBlock (k h : ℕ) (e : BinaryWord) : Prop :=
  ∑ i : Fin h,
      ((e i.1).val : ℚ) * ((k + i.1 + 1 : ℕ) : ℚ) /
        (2 : ℚ) ^ (i.1 + 1) =
    (1 / 2 : ℚ) *
      ∑ i : Fin h,
        ((k + i.1 + 1 : ℕ) : ℚ) /
          (2 : ℚ) ^ (i.1 + 1)

def centralBalancedChain (k : ℕ → ℕ) (e : ℕ → BinaryWord) : Prop :=
  (∀ j : ℕ, Even (k j) ∧ k j < k (j + 1)) ∧
    (∀ j : ℕ,
      balancedBlock (k j) (k (j + 1) - k j) (e j))

def selectedSubset (k : ℕ → ℕ) (e : ℕ → BinaryWord)
    (c : ChoiceSequence) : Set PositiveIndex :=
  {a | ∃ j : ℕ,
    k j < a.1 ∧ a.1 ≤ k (j + 1) ∧
      ((c j).val = 0 ∧
          (e j (a.1 - k j - 1)).val = 1 ∨
       (c j).val = 1 ∧
          (e j (a.1 - k j - 1)).val = 0)}

/-- An infinite consecutive chain of the exact central balanced blocks gives
one representation for every binary choice of a word or its complement, and
these representations are pairwise distinct.  The last equality records the
special value at `k₀ = 0`. -/
def claim46155_continuum_balanced_block_representations : Prop :=
  ∀ (k : ℕ → ℕ) (e : ℕ → BinaryWord),
    centralBalancedChain k e →
    let x : ℚ :=
      ((k 0 + 2 : ℕ) : ℚ) / (2 : ℚ) ^ (k 0 + 1)
    (∀ c : ChoiceSequence,
      subsetRepresentation x (selectedSubset k e c)) ∧
      Function.Injective (selectedSubset k e) ∧
      (k 0 = 0 → x = 1) ∧
      Cardinal.mk (Set.range (selectedSubset k e)) = Cardinal.continuum

end MathlibPlus.Open.NumberTheory

end
