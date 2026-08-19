import MathlibPlus.Open.ResearchFormalization.Claim16071

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization.Claim16071

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

/-- Claim 16070: on the exact finite tree U-polynomial carrier, marking a
connected `k`-component is the sum over deleting that component; applying the
marked-singleton derivative gives the corresponding sum of deleted messages. -/
def claim_16070 : Prop :=
  ∀ {n : ℕ} (T : SimpleGraph (Fin n)) (k : ℕ),
    T.IsTree → 1 ≤ k → k ≤ n →
      (MvPolynomial.pderiv k (treeUPolynomial T) =
          ∑ C ∈ connectedSets T k,
            treeUPolynomial (deletedGraph T C)) ∧
        (MvPolynomial.pderiv k (treeM T) =
          ∑ C ∈ connectedSets T k,
            treeM (deletedGraph T C))

end

end MathlibPlus.Open.ResearchFormalization
