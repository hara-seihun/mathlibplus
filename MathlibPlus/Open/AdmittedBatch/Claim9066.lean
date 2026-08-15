import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.AdmittedBatch

/-- Claim 9066: nonisomorphic equal-edge evaluations are `-1`. -/
def claim_9066_nonisomorphicEqualEdgeEvaluations
    (n : ℕ) (G H : SimpleGraph (Fin n)) : Prop := by
  classical
  exact
    ¬ Nonempty (H ≃g G) →
      H.edgeSet.toFinite.toFinset.card = G.edgeSet.toFinite.toFinset.card →
        let S_G : MvPolynomial (Sym2 (Fin n)) ℤ :=
          ∑ G' ∈
            (Finset.univ.filter
              (fun G' : SimpleGraph (Fin n) => Nonempty (G ≃g G'))),
            ∏ e ∈ G'.edgeSet.toFinite.toFinset, MvPolynomial.X e
        let N_G : ℤ :=
          ((Finset.univ.filter
              (fun G' : SimpleGraph (Fin n) => Nonempty (G ≃g G'))).card : ℤ)
        let m : ℤ := (G.edgeSet.toFinite.toFinset.card : ℤ)
        let T : MvPolynomial (Sym2 (Fin n)) ℤ :=
          ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeSet.toFinite.toFinset,
            MvPolynomial.X e
        let F_G : MvPolynomial (Sym2 (Fin n)) ℤ :=
          MvPolynomial.C (-1) + S_G +
            MvPolynomial.C (N_G + 1) * (MvPolynomial.C m - T)
        let eval_H : MvPolynomial (Sym2 (Fin n)) ℤ → ℤ :=
          MvPolynomial.eval
            (fun e : Sym2 (Fin n) => if e ∈ H.edgeSet then 1 else 0)
        eval_H S_G = 0 ∧ eval_H F_G = -1

end MathlibPlus.Open.AdmittedBatch
