import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Claim 16388: the exact finite graph obstruction underlying the stated
upper bound.  A canonical Ramsey-number definition is not imported here, so
only the premise-matched no-good-graph statement is registered. -/
def noFiveFiveGoodGraphOn46 : Prop :=
  ¬ ∃ G : SimpleGraph (Fin 46),
    G.CliqueFree 5 ∧ G.IndepSetFree 5

end MathlibPlus.Open.GraphTheory
