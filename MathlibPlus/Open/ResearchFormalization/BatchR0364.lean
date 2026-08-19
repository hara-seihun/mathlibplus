import Mathlib
import MathlibPlus.Open.ResearchFormalization.R0364.PairRecurrences

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchR0364

open MathlibPlus.Open.ResearchFormalization.R0364.PairRecurrences

/-- Claim 20445: the canonical unordered profile and its deletion-card sum
use the exact edge bit, common-neighbour count, and min/max exclusive counts
on two-element endpoint sets. -/
def claim20445_canonicalUnorderedPairProfile : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (epsilon : Bool) (c a b : ℕ),
    pairProfile G epsilon c a b =
      Set.ncard {s : Finset V |
        ∃ x y : V,
          s = {x, y} ∧ x ≠ y ∧
            ((epsilon = true) ↔ G.Adj x y) ∧
            (G.commonNeighbors x y).ncard = c ∧
            min (exclusiveCount G x y) (exclusiveCount G y x) = a ∧
            max (exclusiveCount G x y) (exclusiveCount G y x) = b} ∧
    cardProfileSum G epsilon c a b =
      ∑ v : V, pairProfile (deletedGraph G v) epsilon c a b

end MathlibPlus.Open.ResearchFormalization.BatchR0364
