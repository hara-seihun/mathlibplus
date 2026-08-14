import Mathlib

namespace MathlibPlus.Open.NumberTheory.ResearchFormalizationBatch019ffe64

/-- The q=3 moving-gap recurrence.  The gaps and levels are natural numbers,
    as in the source construction. -/
def qThreeMovingGapRecurrence (G : ℕ → ℕ) : Prop :=
  ∀ j : ℕ,
    G (j + 1) = 2 * min (G j) (3 * (j + 3) - G j)

def qThreeFoldAt (G : ℕ → ℕ) (j : ℕ) : Prop :=
  2 * G j > 3 * (j + 3)

def qThreeGapTransitionClaim50525 : Prop :=
  ∀ G : ℕ → ℕ, qThreeMovingGapRecurrence G →
    ∀ j : ℕ,
      (qThreeFoldAt G j ↔
        G (j + 1) = 2 * (3 * (j + 3) - G j)) ∧
      (¬ qThreeFoldAt G j ↔ G (j + 1) = 2 * G j)

/-- The gap obtained after `k` transitions from level `L` without resetting the
    initial gap. -/
def gapAt (d L k : ℕ) : ℕ :=
  Nat.rec d (fun i g => 2 * min g (3 * (L + i + 3) - g)) k

def noFoldAt (d L k : ℕ) : Prop :=
  2 * gapAt d L k ≤ 3 * (L + k + 3)

def foldAt (d L k : ℕ) : Prop :=
  2 * gapAt d L k > 3 * (L + k + 3)

/-- The two first-fold realizability assertions from the q=3 construction. -/
def qThreeFirstFoldRealizationClaim50529 : Prop :=
  (∀ v : ℕ, Odd v → 5 ≤ v → v % 3 ≠ 0 →
    ∃ L k : ℕ,
      (∀ i : ℕ, i < k → noFoldAt 2 L i) ∧
      foldAt 2 L k ∧ gapAt 2 L (k + 1) = 2 * v) ∧
  (∀ v : ℕ, v % 6 = 1 →
    ∃ r k : ℕ,
      Even r ∧ Even (r + k) ∧
      (∀ i : ℕ, i < k → noFoldAt 5 r i) ∧
      foldAt 5 r k ∧ gapAt 5 r (k + 1) = 2 * v)

end MathlibPlus.Open.NumberTheory.ResearchFormalizationBatch019ffe64
