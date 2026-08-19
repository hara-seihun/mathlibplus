import Mathlib
import MathlibPlus.Open.ResearchFormalization.Claim16071

open scoped Classical BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Claim16074

noncomputable section

open MathlibPlus.Open.ResearchFormalization.Claim16071

private noncomputable def maximumBranchDeletionMessages
    {n : ℕ} (T : SimpleGraph (Fin n)) (c : Fin n) (h : ℕ) : UPolynomial :=
  (Finset.univ : Finset (branchIndex T c)).filter
      (fun i : branchIndex T c =>
        Fintype.card (branchVertices T c i) = h) |>.sum
    (fun i : branchIndex T c =>
      treeM (branchDeletionGraph T c i
        (Finset.univ : Finset (branchVertices T c i))))

/-- Claim 16074: at odd order the centroid decomposition specializes exactly
at k=h, and the only residual term is deletion of those centroid branches of
maximum size h. -/
def claim16074_oddEquatorialContinuation : Prop :=
  ∀ {n : ℕ} (T : SimpleGraph (Fin n)) (c : Fin n)
    (r : branchRoots T c) (h : ℕ),
    3 ≤ n →
    n = 2 * h + 1 →
    T.IsTree →
    uniqueCentroidAt T c →
    branchRootsAtCentroid T c r →
    MvPolynomial.pderiv h (treeM T) =
      (branchCoefficientDerivative (centroidProduct T c r)).coeff
          (h + 1) +
        maximumBranchDeletionMessages T c h

end

end MathlibPlus.Open.ResearchFormalization.Claim16074
