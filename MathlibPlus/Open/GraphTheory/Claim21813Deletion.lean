import MathlibPlus.Open.GraphTheory.PinnedGoodBatch

namespace MathlibPlus.Open.GraphTheory

open PinnedGood

/-- Claim 21813: `(5,5)`-goodness is inherited by induced subgraphs, including
vertex deletions from a 43-vertex graph. -/
def claim_21813 : Prop :=
  (∀ {V : Type*} (G : SimpleGraph V),
    IsGood55 G →
      ∀ S : Set V, IsGood55 (G.induce S)) ∧
  (∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
    Fintype.card V = 43 →
      IsGood55 G →
        ∀ v : V,
          IsGood55 (G.induce {w : V | w ≠ v}) ∧
            Nat.card {w : V // w ≠ v} = 42)

end MathlibPlus.Open.GraphTheory
