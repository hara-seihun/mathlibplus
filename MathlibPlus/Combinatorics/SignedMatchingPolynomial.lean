import Mathlib

namespace MathlibPlus.Combinatorics.SignedMatchingPolynomial

open SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Claim 22828: the signed matching polynomial.  Matchings are subgraphs of
`K_n`, so their edges range over all unordered vertex pairs; the ambient graph
contributes the sign of each edge. -/
noncomputable def signedMatchingPolynomial22828 (n : ℕ) (G : SimpleGraph (Fin n)) :
    Polynomial ℤ := by
  classical
  exact
    (Finset.univ.filter (fun M : (⊤ : SimpleGraph (Fin n)).Subgraph => M.IsMatching)).sum
      (fun M =>
        let E : Finset (Sym2 (Fin n)) := M.edgeSet.toFinite.toFinset
        Polynomial.monomial E.card
          (E.prod (fun e => if e ∈ G.edgeSet then (-1 : ℤ) else 1)))

/-- The coefficient of `t^q` is the signed sum over matchings of size `q`. -/
theorem signedMatchingPolynomial22828_coeff (n : ℕ) (G : SimpleGraph (Fin n)) (q : ℕ) :
    (signedMatchingPolynomial22828 n G).coeff q =
      ∑ M ∈ (Finset.univ.filter
          (fun M : (⊤ : SimpleGraph (Fin n)).Subgraph => M.IsMatching)),
        if (M.edgeSet.toFinite.toFinset).card = q then
          (M.edgeSet.toFinite.toFinset).prod
            (fun e => if e ∈ G.edgeSet then (-1 : ℤ) else 1)
        else 0 := by
  classical
  simp [signedMatchingPolynomial22828, Polynomial.coeff_monomial]

end

end MathlibPlus.Combinatorics.SignedMatchingPolynomial
