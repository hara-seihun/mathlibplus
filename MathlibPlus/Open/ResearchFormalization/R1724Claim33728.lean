import Mathlib
import MathlibPlus.Open.Research.FormalizationBatchUPolynomial

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1724Claim33728

noncomputable section
open MathlibPlus.Open.ResearchFormalizationBatch

/-- The displayed complement-of-deleted-edges form of the unrooted
component-size polynomial. -/
def deletedEdgeUPolynomial {V : Type} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) : MvPolynomial ℕ ℤ :=
  (Finset.powerset (uEdgeUniverse B)).sum (fun J =>
    (uComponents (uEdgeUniverse B \ J)).prod
      (fun D => MvPolynomial.X D.card))

/-- Claim 33728: for an unrooted tree, the U-polynomial is the exact sum over
all deleted edge sets and the component-size blocks of the remaining forest. -/
def unrootedTreeUPolynomial_deletedEdges_claim33728 : Prop :=
  ∀ {d : ℕ} (B : SimpleGraph (Fin d)),
    B.IsTree → forestUPolynomial B = deletedEdgeUPolynomial B

end

end MathlibPlus.Open.ResearchFormalization.R1724Claim33728
