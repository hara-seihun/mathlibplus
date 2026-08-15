import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R3173

open scoped BigOperators

noncomputable section

def isLinearFamily {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).card ≤ 1

def isUniformFamily {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (n : ℕ) : Prop :=
  ∀ A ∈ F, A.card = n

def isMatching {α : Type*} [DecidableEq α]
    (M : Finset (Finset α)) : Prop :=
  ∀ A ∈ M, ∀ B ∈ M, A ≠ B → Disjoint A B

def isMaximalMatching {α : Type*} [DecidableEq α]
    (F M : Finset (Finset α)) : Prop :=
  M ⊆ F ∧ isMatching M ∧
    ∀ A ∈ F, A ∉ M → ¬ (∀ B ∈ M, Disjoint A B)

def matchingNumber {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : ℕ := by
  classical
  exact (F.powerset.filter isMatching).sup Finset.card

def groundSet {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Finset α :=
  F.biUnion (fun A => A)

def maximumDegree {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : ℕ := by
  classical
  exact (groundSet F).sup (fun x => (F.filter (fun A => x ∈ A)).card)

/-- A maximal matching covers the family, and its disjoint union has size nν. -/
def maximalMatchingCoverClaim {α : Type*} [DecidableEq α]
    (F M : Finset (Finset α)) (n : ℕ) : Prop :=
  isLinearFamily F ∧ isUniformFamily F n ∧
    isMaximalMatching F M ∧ M.card = matchingNumber F ∧
    (∀ A ∈ F, (A ∩ groundSet M).Nonempty) ∧
    (groundSet M).card = n * matchingNumber F

def isSunflowerWithCore {α : Type*} [DecidableEq α]
    (K : Finset (Finset α))
    (core : Finset α) : Prop :=
  ∀ A ∈ K, ∀ B ∈ K, A ≠ B → A ∩ B = core

def noKSunflower {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (k : ℕ) : Prop :=
  ¬ ∃ (K : Finset (Finset α)) (core : Finset α),
    K ⊆ F ∧ K.card = k ∧ isSunflowerWithCore K core

/-- The core, matching, and maximum-degree consequences of linearity and sunflower-freeness. -/
def linearSunflowerFacts {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  isLinearFamily F ∧
    (∀ K : Finset (Finset α), ∀ core : Finset α,
      K ⊆ F → 3 ≤ K.card →
      isSunflowerWithCore K core → core.card ≤ 1) ∧
    (∀ K : Finset (Finset α), isSunflowerWithCore K ∅ → isMatching K) ∧
    (∀ K : Finset (Finset α), ∀ x : α, K ⊆ F → 3 ≤ K.card →
      isSunflowerWithCore K {x} →
        (∀ A ∈ K, x ∈ A) ∧
        (∀ A ∈ K, ∀ B ∈ K, A ≠ B → A ∩ B = {x})) ∧
    (∀ k, 3 ≤ k → noKSunflower F k →
      matchingNumber F ≤ k - 1 ∧ maximumDegree F ≤ k - 1)

end

end MathlibPlus.Open.ResearchFormalization.R3173
