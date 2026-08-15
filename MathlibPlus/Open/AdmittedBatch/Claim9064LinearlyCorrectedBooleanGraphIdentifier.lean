import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.AdmittedBatch

/-- The linearly corrected Boolean graph identifier from admitted Claim 9064. -/
def claim_9064_linearly_corrected_boolean_graph_identifier
    (n : ℕ) (G : SimpleGraph (Fin n))
    (F_G : MvPolynomial (Sym2 (Fin n)) ℤ) : Prop := by
  classical
  let m : ℕ := G.edgeFinset.card
  let aut_G : Finset (Equiv.Perm (Fin n)) :=
    Finset.univ.filter (fun σ => ∀ v w, G.Adj v w ↔ G.Adj (σ v) (σ w))
  let N_G : ℕ := Nat.factorial n / aut_G.card
  let C_G : ℤ := (N_G : ℤ) + 1
  let copies : Finset (SimpleGraph (Fin n)) :=
    Finset.univ.filter (fun H => Nonempty (G ≃g H))
  let S_G : MvPolynomial (Sym2 (Fin n)) ℤ :=
    ∑ H ∈ copies, ∏ e ∈ H.edgeFinset, MvPolynomial.X e
  let T_X : MvPolynomial (Sym2 (Fin n)) ℤ :=
    ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, MvPolynomial.X e
  exact F_G = -1 + S_G + MvPolynomial.C C_G * (MvPolynomial.C (m : ℤ) - T_X)

end MathlibPlus.Open.AdmittedBatch
