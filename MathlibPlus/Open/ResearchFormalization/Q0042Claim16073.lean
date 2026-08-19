import MathlibPlus.Open.ResearchFormalization.Claim16071

namespace MathlibPlus.Open.ResearchFormalization.Claim16073

open MathlibPlus.Open.ResearchFormalization.Claim16071

/-- The even-order equatorial consequence for a unique-centroid tree. -/
def evenEquatorialContinuation_claim16073 : Prop :=
  ∀ (h : ℕ) (T : SimpleGraph (Fin (2 * h))) (c : Fin (2 * h))
    (r : branchRoots T c),
    T.IsTree →
      uniqueCentroidAt T c →
        branchRootsAtCentroid T c r →
          (∀ i : branchIndex T c,
            Nat.card (branchVertices T c i) ≤ h - 1) ∧
            (∀ C : Finset (Fin (2 * h)),
              C.card = h → connectedVertexSet T C → c ∈ C) ∧
              (branchCoefficientDerivative (centroidProduct T c r)).coeff h =
                MvPolynomial.pderiv h (treeM T)

end MathlibPlus.Open.ResearchFormalization.Claim16073
