import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0343TwoStepDoubleCount

open Classical

noncomputable section

/-- The graph degree as a finite neighbour count. -/
noncomputable def graphDegree_claim20157
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) : ℕ :=
  (Finset.univ.filter (fun x => G.Adj v x)).card

/-- The two-step weight at a vertex, summed over its neighbours. -/
noncomputable def twoStepWeight_claim20157
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) : ℕ :=
  ∑ x : V,
    if G.Adj v x then graphDegree_claim20157 G x - 1 else 0

/-- The two-star count `Σ₂(T)` in the degree convention of the claim. -/
def twoStarCount_claim20157
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  ∑ x : V, Nat.choose (graphDegree_claim20157 G x) 2

/-- The two-step neighbour sum is the degree-weighted double count and twice
 the two-star count. -/
def claim20157 : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V),
    G.IsTree →
    (∑ v : V, twoStepWeight_claim20157 G v) =
        ∑ x : V, graphDegree_claim20157 G x *
          (graphDegree_claim20157 G x - 1) ∧
      (∑ v : V, twoStepWeight_claim20157 G v) =
        2 * twoStarCount_claim20157 G

end
end MathlibPlus.Open.ResearchFormalization.R0343TwoStepDoubleCount
