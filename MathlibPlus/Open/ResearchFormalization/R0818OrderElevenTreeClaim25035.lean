-- UNVERIFIED (downstream): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib
import MathlibPlus.Open.ResearchFormalization.R0818OrderElevenTreeClaims25034_25039

open scoped Sym2

namespace MathlibPlus.Open.ResearchFormalization.R0818OrderElevenTree

noncomputable section

/-- A concrete representative of `P₃ ⊔ H₇`: vertices `0,1,2` form the
three-vertex path, while `3` is the degree-three vertex of the seven-vertex
component and `3-4-5-6-7` is its arm of length four. -/
def p3H7Edges : Finset (Sym2 (Fin 10)) :=
  {s(0, 1), s(1, 2),
   s(3, 4), s(4, 5), s(5, 6), s(6, 7), s(3, 8), s(3, 9)}

def p3H7Forest : SimpleGraph (Fin 10) :=
  SimpleGraph.fromEdgeSet (p3H7Edges : Set (Sym2 (Fin 10)))

/-- Claim 25035: the two exact deletion forests of the explicit tree have the
common unrooted type `P₃ ⊔ H₇`. -/
def commonDeletionForestType_claim25035 : Prop :=
  Nonempty (deletedForest 0 ≃g p3H7Forest) ∧
    Nonempty (deletedForest 5 ≃g p3H7Forest)

end

end MathlibPlus.Open.ResearchFormalization.R0818OrderElevenTree
