import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_019ffedf

namespace MathlibPlus.Open.ResearchFormalization.R0668Claim29507

open MathlibPlus.Open.ResearchFormalizationBatch_019ffedf

/-- Claim 29507: the four-part redundantly connected cycle blow-up is the
complete bipartite graph with parts of size 2n. -/
def claim29507 : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    graphIsomorphic (rccHost n 4)
      (SimpleGraph.completeMultipartiteGraph
        (fun _ : Fin 2 => Fin (2 * n)))

end MathlibPlus.Open.ResearchFormalization.R0668Claim29507
