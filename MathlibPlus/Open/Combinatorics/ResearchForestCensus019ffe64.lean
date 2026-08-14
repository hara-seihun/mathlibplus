import Mathlib

namespace MathlibPlus.Open.Combinatorics.ResearchFormalizationBatch019ffe64

open scoped BigOperators

noncomputable section

/-- The graph carrying a selected edge set.  Its connected components are the
    components covered by the selected-edge forest. -/
def selectedEdgeGraph {V : Type*} (A : Finset (Sym2 V)) : SimpleGraph V := by
  classical
  exact SimpleGraph.fromRel (fun v w => s(v, w) ∈ A)

/-- Number of nontrivial connected components of the selected-edge graph. -/
def coveredComponentCount {V : Type*} [Fintype V]
    (A : Finset (Sym2 V)) : ℕ :=
  ((Finset.univ : Finset (selectedEdgeGraph A).ConnectedComponent).filter
    (fun c => 2 ≤ c.supp.ncard)).card

/-- The covered-component polynomial of a finite simple graph, with the inner
    variable representing `x` and the outer variable representing `y`. -/
def forestCoveredPolynomial {V : Type*} [Fintype V]
    (F : SimpleGraph V) : Polynomial (Polynomial ℚ) := by
  classical
  exact Finset.sum F.edgeFinset.powerset (fun a =>
    Polynomial.monomial (coveredComponentCount a)
      (Polynomial.monomial a.card (1 : ℚ)))

/-- The polynomial for deleting a vertex set before forming the selected-edge
    forest.  Edges incident with the deleted set are excluded. -/
def forestDeletedCoveredPolynomial {V : Type*} [Fintype V]
    (F : SimpleGraph V) (S : Finset V) : Polynomial (Polynomial ℚ) := by
  classical
  exact Finset.sum (F.edgeFinset.filter
      (fun e => Disjoint e.toFinset S)).powerset (fun a =>
    Polynomial.monomial (coveredComponentCount a)
      (Polynomial.monomial a.card (1 : ℚ)))

/-- The three-variable marked polynomial, with the outer variable representing
    `q`. -/
def forestMarkedPolynomial {V : Type*} [Fintype V]
    (F : SimpleGraph V) : Polynomial (Polynomial (Polynomial ℚ)) := by
  classical
  exact Finset.sum (Finset.univ : Finset (Finset V)) (fun s =>
    if 2 ≤ s.card ∧ (F.induce (s : Set V)).Connected then
      Polynomial.monomial (s.card - 1)
        (Polynomial.C (Polynomial.monomial (s.card - 1) (1 : ℚ)) *
          forestDeletedCoveredPolynomial F s)
    else 0)

/-- The same marked polynomial after specializing the middle variable `y` to
    one. -/
def forestMarkedAtYOne {V : Type*} [Fintype V]
    (F : SimpleGraph V) : Polynomial (Polynomial ℚ) := by
  classical
  exact Finset.sum (Finset.univ : Finset (Finset V)) (fun s =>
    if 2 ≤ s.card ∧ (F.induce (s : Set V)).Connected then
      Polynomial.monomial (s.card - 1)
        (Polynomial.monomial (s.card - 1) (1 : ℚ) *
          (forestDeletedCoveredPolynomial F s).eval (1 : Polynomial ℚ))
    else 0)

/-- `M_F(x,y,1) = ∂_y C_F(x,y)`, together with its stated consequence. -/
def markedForestDerivativeClaim50487 : Prop :=
  ∀ {V : Type*} [Fintype V] (F : SimpleGraph V),
    F.IsAcyclic →
      ((forestMarkedPolynomial F).eval (1 : Polynomial (Polynomial ℚ)) =
          Polynomial.derivative (forestCoveredPolynomial F)) ∧
      (∀ {G : SimpleGraph V}, G.IsAcyclic →
        forestCoveredPolynomial F = forestCoveredPolynomial G →
        (forestMarkedPolynomial F).eval (1 : Polynomial (Polynomial ℚ)) =
          (forestMarkedPolynomial G).eval (1 : Polynomial (Polynomial ℚ)))

/-- Number of selected connected vertex sets with a prescribed order and
    boundary size. -/
def boundaryEdgeCount {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) : ℕ := by
  classical
  exact (T.edgeFinset.filter
    (fun e => (e.toFinset ∩ S).card = 1)).card

def connectedSubtreeCount {n : ℕ}
    (T : SimpleGraph (Fin n)) (k b : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Finset (Fin n))).filter
    (fun (s : Finset (Fin n)) => 2 ≤ s.card ∧ s.card = k ∧
      (T.induce (s : Set (Fin n))).Connected ∧
      boundaryEdgeCount T s = b)).card

/-- The `y=1` census transform, represented as a polynomial in `q` whose
    coefficients are polynomials in `x`. -/
def markedCensusPolynomial {n : ℕ}
    (T : SimpleGraph (Fin n)) : Polynomial (Polynomial ℚ) := by
  classical
  let term : ℕ → ℕ → Polynomial (Polynomial ℚ) := fun k b =>
    Polynomial.monomial (k - 1)
      ((connectedSubtreeCount T k b : ℚ) •
        (Polynomial.monomial (k - 1) (1 : ℚ) *
          (1 + Polynomial.X) ^ (n - k - b)))
  exact Finset.sum (Finset.range (n + 1)) (fun k =>
    Finset.sum (Finset.range (n + 1)) (term k))

/-- The order/boundary transform and its injectivity assertion for trees. -/
def markedTreeCensusClaim50488 : Prop :=
  ∀ (n : ℕ) (T : SimpleGraph (Fin n)),
    T.IsTree →
      forestMarkedAtYOne T = markedCensusPolynomial T ∧
      (∀ (U : SimpleGraph (Fin n)), U.IsTree →
        (forestMarkedAtYOne T = forestMarkedAtYOne U ↔
          ∀ k b : ℕ, connectedSubtreeCount T k b =
            connectedSubtreeCount U k b))

end

end MathlibPlus.Open.Combinatorics.ResearchFormalizationBatch019ffe64
