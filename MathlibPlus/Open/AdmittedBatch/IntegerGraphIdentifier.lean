import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.AdmittedBatch

/-- The distinct labeled copies of `G` on the fixed vertex set `Fin n`. -/
def integerGraphOrbitCopies
    (n : ℕ) (G : SimpleGraph (Fin n)) : Finset (SimpleGraph (Fin n)) := by
  classical
  exact Finset.univ.filter (fun G' : SimpleGraph (Fin n) => Nonempty (G ≃g G'))

/-- The orbit-sum polynomial with integer coefficients. -/
def integerGraphOrbitSum
    (n : ℕ) (G : SimpleGraph (Fin n)) : MvPolynomial (Sym2 (Fin n)) ℤ := by
  classical
  exact
    ∑ G' ∈ integerGraphOrbitCopies n G,
      ∏ e ∈ G'.edgeSet.toFinite.toFinset, MvPolynomial.X e

/-- The number of edges of `G`. -/
def integerGraphEdgeCount
    (n : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  G.edgeSet.toFinite.toFinset.card

/-- The complete-graph edge-variable sum. -/
def integerCompleteGraphEdgeSum
    (n : ℕ) : MvPolynomial (Sym2 (Fin n)) ℤ := by
  classical
  exact
    ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeSet.toFinite.toFinset,
      MvPolynomial.X e

/-- The integer-coefficient Boolean graph identifier from Claim 9068. -/
def integerGraphIdentifier
    (n : ℕ) (G : SimpleGraph (Fin n)) : MvPolynomial (Sym2 (Fin n)) ℤ :=
  (-1 : MvPolynomial (Sym2 (Fin n)) ℤ) + integerGraphOrbitSum n G +
    MvPolynomial.C (((integerGraphOrbitCopies n G).card + 1 : ℕ) : ℤ) *
      (MvPolynomial.C (integerGraphEdgeCount n G : ℤ) -
        integerCompleteGraphEdgeSum n)

/-- Claim 9068: integer coefficients suffice, with the exact Boolean zero set. -/
def claim_9068_integer_coefficients_suffice : Prop := by
  classical
  exact
    ∀ (n : ℕ) (G H : SimpleGraph (Fin n)),
      MvPolynomial.eval
          (fun e : Sym2 (Fin n) => if e ∈ H.edgeSet then 1 else 0)
          (integerGraphIdentifier n G) = 0 ↔ Nonempty (G ≃g H)

end MathlibPlus.Open.AdmittedBatch
