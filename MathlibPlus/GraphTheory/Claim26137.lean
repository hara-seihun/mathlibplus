import MathlibPlus.Basic

namespace MathlibPlus.GraphTheory.Claim26137

/-- A finite simple graph is cyclic-five when every five-vertex induced
subgraph contains a cycle.  `¬ IsAcyclic` records “contains a cycle” without
requiring the induced subgraph itself to be a five-cycle. -/
def cyclicFive {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, s.card = 5 → ¬ (G.induce s).IsAcyclic

end MathlibPlus.GraphTheory.Claim26137
