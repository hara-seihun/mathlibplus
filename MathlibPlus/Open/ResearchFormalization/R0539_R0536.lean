import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0539_R0536

/-- The induced-forest-number condition, expressed directly by induced acyclicity. -/
def inducedForestNumberAtMostFour {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) : Prop :=
  ∀ S : Finset V,
    H.induce (S : Set V) |>.IsAcyclic → S.card ≤ 4

/-- The number of edges of a finite simple graph. -/
noncomputable def finiteEdgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) : ℕ :=
  Nat.card H.edgeSet

/-- Claim 22437: the sharp induced-forest-four edge bound. -/
def claim22437 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (n : ℕ),
    Fintype.card V = n →
    8 ≤ n →
    inducedForestNumberAtMostFour H →
    finiteEdgeCount H ≥
      Nat.ceil (((n : ℚ) * ((n - 2 : ℕ) : ℚ)) / 4)

end MathlibPlus.Open.ResearchFormalization.R0539_R0536
