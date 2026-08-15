import Mathlib

open scoped BigOperators
open Classical
noncomputable section

namespace MathlibPlus.Open

abbrev UnionClosedFamily (α : Type*) := Finset (Finset α)

def ordinaryUnionClosed {α : Type*} [DecidableEq α]
    (F : UnionClosedFamily α) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F

def outsideSupport {α : Type*} [DecidableEq α]
    (M A : Finset α) : Finset α := A \ M

def traceOn {α : Type*} [DecidableEq α]
    (M A : Finset α) : Finset α := A ∩ M

def outsideSupportFamily {α : Type*} [DecidableEq α]
    (F : UnionClosedFamily α) (M : Finset α) : Finset (Finset α) :=
  F.image (outsideSupport M)

def traceFiber {α : Type*} [DecidableEq α]
    (F : UnionClosedFamily α) (M S : Finset α) : Finset (Finset α) :=
  (F.filter (fun A => outsideSupport M A = S)).image (traceOn M)

def tracePairwiseUnion {α : Type*} [DecidableEq α]
    (H R : Finset (Finset α)) : Finset (Finset α) :=
  H.biUnion (fun T => R.image (fun U => T ∪ U))

def fiberUnionClosed {α : Type*} [DecidableEq α]
    (F : UnionClosedFamily α) (M S : Finset α) : Prop :=
  ∀ T ∈ traceFiber F M S, ∀ U ∈ traceFiber F M S,
    T ∪ U ∈ traceFiber F M S

def fiberContainsTop {α : Type*} [DecidableEq α]
    (F : UnionClosedFamily α) (M S : Finset α) : Prop :=
  M ∈ traceFiber F M S

def supportUnionClosed {α : Type*} [DecidableEq α]
    (F : UnionClosedFamily α) (M : Finset α) : Prop :=
  ∀ S ∈ outsideSupportFamily F M, ∀ R ∈ outsideSupportFamily F M,
    S ∪ R ∈ outsideSupportFamily F M

def fiberPairwiseUnionIncluded {α : Type*} [DecidableEq α]
    (F : UnionClosedFamily α) (M S R : Finset α) : Prop :=
  tracePairwiseUnion (traceFiber F M S) (traceFiber F M R) ⊆
    traceFiber F M (S ∪ R)

/-- Three-set trace fibers and their exact union-closure transport. -/
def formalizationClaim46768 {α : Type*} [Fintype α] [DecidableEq α]
    (F : UnionClosedFamily α) (M : Finset α) : Prop :=
  M ∈ F ∧ M.card = 3 ∧ ordinaryUnionClosed F →
    (∀ S ∈ outsideSupportFamily F M,
      fiberContainsTop F M S ∧ fiberUnionClosed F M S) ∧
    supportUnionClosed F M ∧
    (∀ S ∈ outsideSupportFamily F M, ∀ R ∈ outsideSupportFamily F M,
      fiberPairwiseUnionIncluded F M S R)

def traceExcess {α : Type*} (H : Finset (Finset α)) : ℤ :=
  (H.card : ℤ) - 2

def principalFilterDeficit {α : Type*} [DecidableEq α]
    (F : UnionClosedFamily α) (M : Finset α) : ℤ :=
  (F.card : ℤ) - 2 * (F.filter (fun A => M ⊆ A)).card

def fiberExcessSum {α : Type*} [DecidableEq α]
    (F : UnionClosedFamily α) (M : Finset α) : ℤ :=
  ∑ S ∈ outsideSupportFamily F M, traceExcess (traceFiber F M S)

/-- The exact fiber-excess identity and the two distinguished excesses. -/
def formalizationClaim46770 {α : Type*} [Fintype α] [DecidableEq α]
    (F : UnionClosedFamily α) (M : Finset α) : Prop :=
  M ∈ F ∧ M.card = 3 ∧ ordinaryUnionClosed F →
    (F.filter (fun A => M ⊆ A)).card = (outsideSupportFamily F M).card ∧
    principalFilterDeficit F M = fiberExcessSum F M ∧
    traceExcess ({∅, M} : Finset (Finset α)) = 0 ∧
    traceExcess ({M} : Finset (Finset α)) = -1

/-- The combined three-set fiber statement, retained independently. -/
def formalizationClaim46780 {α : Type*} [Fintype α] [DecidableEq α]
    (F : UnionClosedFamily α) (M : Finset α) : Prop :=
  M ∈ F ∧ M.card = 3 ∧ ordinaryUnionClosed F →
    (∀ S ∈ outsideSupportFamily F M,
      M ∈ traceFiber F M S ∧ fiberUnionClosed F M S) ∧
    supportUnionClosed F M ∧
    (∀ S ∈ outsideSupportFamily F M, ∀ R ∈ outsideSupportFamily F M,
      fiberPairwiseUnionIncluded F M S R) ∧
    principalFilterDeficit F M = fiberExcessSum F M ∧
    traceExcess ({∅, M} : Finset (Finset α)) = 0 ∧
    traceExcess ({M} : Finset (Finset α)) = -1

end MathlibPlus.Open
