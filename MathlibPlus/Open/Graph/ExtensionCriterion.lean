import Mathlib

namespace MathlibPlus.Open.Graph.ExtensionCriterion

/-- A finite set is a clique when every pair of distinct members is adjacent. -/
def PairwiseAdjacent {V : Type*} (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ s → v ∈ s → u ≠ v → G.Adj u v

/-- A finite set is independent when every pair of distinct members is non-adjacent. -/
def PairwiseNonadjacent {V : Type*} (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ s → v ∈ s → u ≠ v → ¬G.Adj u v

/-- The `(5,5)`-good property: no five-vertex clique and no five-vertex independent set. -/
def Good55 {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ¬ ∃ s : Finset V, s.card = 5 ∧
    (PairwiseAdjacent G s ∨ PairwiseNonadjacent G s)

/-- Add one vertex whose old-vertex adjacency is recorded by a Boolean assignment. -/
def ExtendByBool {V : Type*} (G : SimpleGraph V) (x : V → Bool) :
    SimpleGraph (Option V) :=
  SimpleGraph.fromRel fun a b =>
    match a, b with
    | some u, some v => G.Adj u v
    | none, some v => x v = true
    | some u, none => x u = true
    | none, none => False

/-- Every old four-clique avoids the all-true assignment. -/
def K4ExtensionClause {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (x : V → Bool) : Prop :=
  ∀ s : Finset V, s.card = 4 → PairwiseAdjacent G s →
    ¬ ∀ v ∈ s, x v = true

/-- Every old independent four-set meets the true assignment. -/
def Independent4ExtensionClause {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (x : V → Bool) : Prop :=
  ∀ s : Finset V, s.card = 4 → PairwiseNonadjacent G s →
    ∃ v ∈ s, x v = true

/-- Claim 12667: the two old-four-set clause families exactly characterize a good extension. -/
def claim12667 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (x : V → Bool),
    Good55 G →
      (Good55 (ExtendByBool G x) ↔
        (K4ExtensionClause G x ∧ Independent4ExtensionClause G x))

/-- Claim 12668: complementation exchanges the two clause families and
preserves extension satisfiability. -/
def claim12668 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (x : V → Bool),
    (K4ExtensionClause G x ↔
        Independent4ExtensionClause (Gᶜ) (fun v => !x v)) ∧
    (Independent4ExtensionClause G x ↔
        K4ExtensionClause (Gᶜ) (fun v => !x v)) ∧
    (Good55 (ExtendByBool G x) ↔
        Good55 (ExtendByBool (Gᶜ) (fun v => !x v)))

end MathlibPlus.Open.Graph.ExtensionCriterion
