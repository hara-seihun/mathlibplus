import Mathlib

namespace MathlibPlus.Open.GraphTheory.Claim43511

/-- Claim 43511: on a finite labeled vertex type, edge containment together
with equal finite edge cardinality forces equality of simple graphs. -/
def claim43511 : Prop :=
  ∀ {Vertex : Type*} [Fintype Vertex]
    (source host : SimpleGraph Vertex)
    [DecidableRel source.Adj] [DecidableRel host.Adj],
    source ≤ host →
      source.edgeFinset.card = host.edgeFinset.card →
        source = host

end MathlibPlus.Open.GraphTheory.Claim43511
