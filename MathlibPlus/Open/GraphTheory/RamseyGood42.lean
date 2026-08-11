import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Claim 9139: a simple graph on 42 vertices with neither a five-clique nor
an independent set of size five exists. -/
def existsFiveFiveGoodGraphOn42 : Prop :=
  ∃ G : SimpleGraph (Fin 42),
    G.CliqueFree 5 ∧ G.IndepSetFree 5

end MathlibPlus.Open.GraphTheory
