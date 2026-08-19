import Mathlib
import MathlibPlus.Open.Research.FormalizationR0375

namespace MathlibPlus.Open.ResearchFormalization.R0375Claim20575

noncomputable section

open Classical
attribute [local instance] Classical.propDecidable Classical.decEq

open MathlibPlus.Open.Research.R0375

private def diamondGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel (fun u v : Fin 4 =>
    u ≠ v ∧
      ¬ ((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0)))

private def diamondSpanningTrees :
    Finset (SimpleGraph (Fin 4)) :=
  (Finset.univ : Finset (SimpleGraph (Fin 4))).filter
    (fun T => T ≤ diamondGraph ∧ T.IsTree)

/-- Claim 20575: the fixed labeled diamond has exactly eight spanning trees,
and their distinct host-orbit incidences form the singleton `{3}`. -/
def diamondHasEightSpanningTrees_claim20575 : Prop :=
  diamondSpanningTrees.card = 8 ∧
    diamondSpanningTrees.image (hostOrbitIncidence 4 diamondGraph) =
      ({3} : Finset ℕ)

end

end MathlibPlus.Open.ResearchFormalization.R0375Claim20575
