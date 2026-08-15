import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.AdmittedBatch

/-- Claim 9059: the spanning subgraph-count orbit sum. -/
def spanningSubgraphCountOrbitSum
    (n : ℕ) (G : SimpleGraph (Fin n))
    (S : MvPolynomial (Sym2 (Fin n)) ℕ) : Prop := by
  classical
  exact
    S =
      ∑ G' ∈
          (Finset.univ.filter
            (fun G' : SimpleGraph (Fin n) => Nonempty (G ≃g G'))),
        ∏ e ∈ G'.edgeSet.toFinite.toFinset, MvPolynomial.X e

/-- Claim 9060: Boolean adjacency evaluation counts spanning copies. -/
def orbitSumBooleanEvaluationCountsSpanningCopies
    (n : ℕ) (G H : SimpleGraph (Fin n)) : Prop := by
  classical
  exact
    MvPolynomial.eval
        (fun e : Sym2 (Fin n) => if e ∈ H.edgeSet then 1 else 0)
        (∑ G' ∈
            (Finset.univ.filter
              (fun G' : SimpleGraph (Fin n) => Nonempty (G ≃g G'))),
          ∏ e ∈ G'.edgeSet.toFinite.toFinset, MvPolynomial.X e) =
      ((Finset.univ.filter
          (fun G' : SimpleGraph (Fin n) => Nonempty (G ≃g G'))).filter
        (fun G' => G' ≤ H)).card

end MathlibPlus.Open.AdmittedBatch
