import Mathlib

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization.R0364.PairRecurrences

noncomputable section

/-- The edge bit used by the canonical pair profile. -/
def edgeProfile {V : Type*} (G : SimpleGraph V) (ε : Bool) (x y : V) : Prop :=
  (ε = true) ↔ G.Adj x y

/-- Common neighbours of a pair. -/
def commonCount {V : Type*} (G : SimpleGraph V) (x y : V) : ℕ :=
  (G.commonNeighbors x y).ncard

/-- Neighbours exclusive to the first endpoint, with the other endpoint removed. -/
def exclusiveCount {V : Type*} (G : SimpleGraph V) (x y : V) : ℕ :=
  (G.neighborSet x \ (G.neighborSet y ∪ {y})).ncard

/-- The exact unordered-pair predicate underlying the canonical profile. -/
def unorderedPairData {V : Type*} (G : SimpleGraph V) (ε : Bool)
    (c a b : ℕ) (s : Finset V) : Prop :=
  ∃ x y : V,
    s = {x, y} ∧ x ≠ y ∧
      edgeProfile G ε x y ∧
      commonCount G x y = c ∧
      min (exclusiveCount G x y) (exclusiveCount G y x) = a ∧
      max (exclusiveCount G x y) (exclusiveCount G y x) = b

/-- The canonical unordered-pair profile p_ε(c,a,b;G). -/
noncomputable def pairProfile {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ε : Bool) (c a b : ℕ) : ℕ :=
  Set.ncard {s : Finset V | unorderedPairData G ε c a b s}

/-- The graph card obtained by deleting a vertex, on the surviving subtype. -/
def deletedGraph {V : Type*} (G : SimpleGraph V) (v : V) :
    SimpleGraph {u : V // u ≠ v} :=
  G.induce {u : V | u ≠ v}

/-- The deleted-card sum S_ε(c,a,b;G). -/
noncomputable def cardProfileSum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ε : Bool) (c a b : ℕ) : ℕ :=
  ∑ v : V, pairProfile (deletedGraph G v) ε c a b

/-- Equal-side deck recurrence with integer coefficients for the displayed count identity. -/
def claim20446_equalSideDeckRecurrence : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ε : Bool) (c a : ℕ),
    (cardProfileSum G ε c a a : ℤ) =
      ((Fintype.card V : ℤ) - 2 - (c : ℤ) - 2 * (a : ℤ)) *
          (pairProfile G ε c a a : ℤ) +
        ((c : ℤ) + 1) * (pairProfile G ε (c + 1) a a : ℤ) +
        ((a : ℤ) + 1) * (pairProfile G ε c a (a + 1) : ℤ)

/-- Unequal-side deck recurrence, including the doubled adjacent-side source. -/
def claim20447_unequalSideDeckRecurrence : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ε : Bool) (c a b : ℕ), a < b →
    (cardProfileSum G ε c a b : ℤ) =
      ((Fintype.card V : ℤ) - 2 - (c : ℤ) - (a : ℤ) - (b : ℤ)) *
          (pairProfile G ε c a b : ℤ) +
        ((c : ℤ) + 1) * (pairProfile G ε (c + 1) a b : ℤ) +
        ((a : ℤ) + 1) *
          (1 + if b = a + 1 then (1 : ℤ) else 0) *
          (pairProfile G ε c (a + 1) b : ℤ) +
        ((b : ℤ) + 1) * (pairProfile G ε c a (b + 1) : ℤ)

end
end MathlibPlus.Open.ResearchFormalization.R0364.PairRecurrences
