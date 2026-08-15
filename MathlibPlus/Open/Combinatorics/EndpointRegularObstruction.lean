import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- A five-vertex clique in a finite simple graph. -/
def HasFiveClique {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ s : Set V,
    s.ncard = 5 ∧
      ∀ ⦃v w : V⦄, v ∈ s → w ∈ s → v ≠ w → G.Adj v w

/-- A five-vertex independent set in a finite simple graph. -/
def HasFiveIndependentSet {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ s : Set V,
    s.ncard = 5 ∧
      ∀ ⦃v w : V⦄, v ∈ s → w ∈ s → v ≠ w → ¬G.Adj v w

/-- Every vertex has the specified degree. -/
def IsRegularOfDegree {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ v : V, (G.neighborSet v).ncard = d

/--
Endpoint-regular obstruction: a finite simple graph with no five-clique and no
five-vertex independent set cannot have order 43, 44, or 45 and be regular of
endpoint degree `n - 25` or degree 24.
-/
def endpointRegularObstruction : Prop :=
  ∀ {V : Type*} [Fintype V] (G : SimpleGraph V) (n : ℕ),
    Fintype.card V = n →
      (n = 43 ∨ n = 44 ∨ n = 45) →
        ¬HasFiveClique G →
          ¬HasFiveIndependentSet G →
            (¬IsRegularOfDegree G (n - 25) ∧ ¬IsRegularOfDegree G 24)

end MathlibPlus.Open.Combinatorics
