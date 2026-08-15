import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.AdmittedBatch

private def graphCopies {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (SimpleGraph (Fin n)) := by
  classical
  exact Finset.univ.filter (fun G' : SimpleGraph (Fin n) => Nonempty (G ≃g G'))

private def graphEdgeCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  G.edgeSet.toFinite.toFinset.card

private def graphNonisolatedVertexCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun v : Fin n => ∃ w, G.Adj v w)).card

private def monomialVertexSupport {n : ℕ} (d : Sym2 (Fin n) →₀ ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v => ∃ e ∈ d.support, v ∈ e)

private def polynomialSupportDegree {n : ℕ}
    (P : MvPolynomial (Sym2 (Fin n)) ℤ) : ℕ :=
  P.support.sup (fun d => (monomialVertexSupport d).card)

private def spanningSubgraphCount {n : ℕ} (G : SimpleGraph (Fin n)) :
    MvPolynomial (Sym2 (Fin n)) ℤ := by
  classical
  exact
    ∑ G' ∈ graphCopies G,
      ∏ e ∈ G'.edgeSet.toFinite.toFinset,
        (MvPolynomial.X e : MvPolynomial (Sym2 (Fin n)) ℤ)

private def graphIdentifier {n : ℕ} (G : SimpleGraph (Fin n)) :
    MvPolynomial (Sym2 (Fin n)) ℤ := by
  classical
  let T : MvPolynomial (Sym2 (Fin n)) ℤ :=
    ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeSet.toFinite.toFinset,
      (MvPolynomial.X e : MvPolynomial (Sym2 (Fin n)) ℤ)
  exact
    (-1 : MvPolynomial (Sym2 (Fin n)) ℤ) + spanningSubgraphCount G +
      MvPolynomial.C (((graphCopies G).card : ℤ) + 1) *
        (MvPolynomial.C (graphEdgeCount G : ℤ) - T)

private def evaluateOnGraph {n : ℕ}
    (P : MvPolynomial (Sym2 (Fin n)) ℤ) (H : SimpleGraph (Fin n)) : ℤ := by
  classical
  exact MvPolynomial.eval (fun e => if e ∈ H.edgeSet then 1 else 0) P

private def isGraphIdentifier {n : ℕ} (G : SimpleGraph (Fin n))
    (P : MvPolynomial (Sym2 (Fin n)) ℤ) : Prop :=
  ∀ H : SimpleGraph (Fin n),
    evaluateOnGraph P H = 0 ↔ Nonempty (G ≃g H)

private def complementPullback {n : ℕ}
    (P : MvPolynomial (Sym2 (Fin n)) ℤ) : MvPolynomial (Sym2 (Fin n)) ℤ :=
  MvPolynomial.eval₂ MvPolynomial.C
    (fun e => 1 - MvPolynomial.X e) P

private def minimumComplementIdentifier {n : ℕ} (G : SimpleGraph (Fin n)) :
    MvPolynomial (Sym2 (Fin n)) ℤ :=
  if graphEdgeCount G ≤ graphEdgeCount (Gᶜ) then
    graphIdentifier G
  else
    complementPullback (graphIdentifier (Gᶜ))

/-- Claim 9072: choosing the smaller of a graph and its Boolean complement and
pulling the identifier back through complementation preserves identification,
with the stated ordinary-degree and vertex-support-degree bounds. -/
def minimumOfComplementsIdentifierBounds : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    isGraphIdentifier G (minimumComplementIdentifier G) ∧
      MvPolynomial.totalDegree (minimumComplementIdentifier G) ≤
        max 1 (min (graphEdgeCount G) (Nat.choose n 2 - graphEdgeCount G)) ∧
      polynomialSupportDegree (minimumComplementIdentifier G) ≤
        max 2 (min (graphNonisolatedVertexCount G)
          (graphNonisolatedVertexCount (Gᶜ)))

end MathlibPlus.Open.AdmittedBatch
