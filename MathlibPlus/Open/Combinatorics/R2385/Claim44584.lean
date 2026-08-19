import Mathlib

namespace MathlibPlus.Open.Combinatorics.R2385

/-- Claim 44584: every 44-vertex simple graph avoiding both 5-cliques and
5-independent sets is neither 19-regular nor 24-regular. -/
def noNineteenOrTwentyFourRegularGraph_claim44584 : Prop :=
  ∀ G : SimpleGraph (Fin 44),
    SimpleGraph.CliqueFree G 5 →
      SimpleGraph.CliqueFree (Gᶜ) 5 →
        (¬ (∀ v : Fin 44, Set.ncard (G.neighborSet v) = 19)) ∧
          ¬ (∀ v : Fin 44, Set.ncard (G.neighborSet v) = 24)

end MathlibPlus.Open.Combinatorics.R2385
