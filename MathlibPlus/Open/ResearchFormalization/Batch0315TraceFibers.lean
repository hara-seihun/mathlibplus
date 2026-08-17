import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch0315TraceFibers

open scoped BigOperators

def familyUnion {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Finset α :=
  F.biUnion (fun A => A)

def tightCoordinates {α : Type*} [DecidableEq α]
    (t : Fin 3 → α) : Finset α :=
  Finset.univ.image t

def unionClosedFamily {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  ∀ ⦃A B : Finset α⦄, A ∈ F → B ∈ F → A ∪ B ∈ F

def fullTraceProjection {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (t : Fin 3 → α) : Prop :=
  ∀ A ∈ (tightCoordinates t).powerset,
    ∃ C ∈ F, C ∩ tightCoordinates t = A

def traceFiber {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (t : Fin 3 → α) (A : Finset α) :
    Finset (Finset α) :=
  (familyUnion F \ tightCoordinates t).powerset.filter
    (fun B => A ∪ B ∈ F)

def traceWeight {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (t : Fin 3 → α) (A : Finset α) : ℕ :=
  (traceFiber F t A).card

def traceExcess {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (t : Fin 3 → α) (A : Finset α) : ℕ :=
  traceWeight F t A - 1

/-- Claim 19710: the three-coordinate trace fibers use every subset of the
outside union, and a full projection supplies the one-member skeleton. -/
def traceFibersAndTightCubeExcess : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (t : Fin 3 → α),
    Function.Injective t →
    unionClosedFamily F →
    fullTraceProjection F t →
    ∀ A ∈ (tightCoordinates t).powerset,
      1 ≤ traceWeight F t A ∧
      traceExcess F t A = traceWeight F t A - 1

end MathlibPlus.Open.ResearchFormalization.Batch0315TraceFibers
