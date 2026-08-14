import Mathlib

namespace MathlibPlus.Open.Research.TreeCuts

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The finite edge set of a finite simple graph. -/
def graphEdges {V : Type} [Fintype V] (T : SimpleGraph V) : Finset (Sym2 V) :=
  (Finset.univ.filter (fun e : Sym2 V => e ∈ T.edgeSet))

/-- A subset of the edge set, interpreted as the edges deleted from a graph. -/
def TreeEdgeSubset {V : Type} [Fintype V] (T : SimpleGraph V) :=
  {S : Finset (Sym2 V) // S ⊆ graphEdges T}

instance treeEdgeSubsetFintype {V : Type} [Fintype V] (T : SimpleGraph V) :
    Fintype (TreeEdgeSubset T) := Subtype.fintype _

/-- An edge crosses the blocks of a vertex partition when its endpoints are inequivalent. -/
def partitionEdgeRelation {V : Type} (p : Setoid V) : Sym2 V → Prop :=
  Sym2.lift ⟨
    (fun a b : V => ¬p.r a b),
    (by
      intro a b
      apply propext
      constructor
      · intro h hab
        exact h (p.symm hab)
      · intro h hba
        exact h (p.symm hba))⟩

def crossingEdges {V : Type} [Fintype V] (T : SimpleGraph V) (p : Setoid V) :
    TreeEdgeSubset T :=
  ⟨(graphEdges T).filter (partitionEdgeRelation p), by
    intro e he
    exact (Finset.mem_filter.mp he).1⟩

/-- The component relation after deleting the edge subset S. -/
def partitionFromCut {V : Type} [Fintype V] (T : SimpleGraph V)
    (S : TreeEdgeSubset T) : Setoid V :=
  Relation.EqvGen.setoid (fun a b : V => T.Adj a b ∧ s(a, b) ∉ S.1)

/-- Set partitions whose every induced block is connected. -/
def ConnectedPartition {V : Type} [Fintype V] (T : SimpleGraph V) :=
  {p : Setoid V // ∀ v : V, (T.induce {u : V | p.r u v}).Connected}

/-- Claim 19875. -/
def claim19875 : Prop :=
  ∀ {V : Type} [Fintype V] (T : SimpleGraph V), T.IsTree →
    ∃ f : ConnectedPartition T ≃ TreeEdgeSubset T,
      (∀ p : ConnectedPartition T, f p = crossingEdges T p.1) ∧
      (∀ S : TreeEdgeSubset T, (f.symm S).1 = partitionFromCut T S)

/-- The component-size monomial of a finite equivalence relation. -/
def componentMonomial {V : Type} [Fintype V] (p : Setoid V) : MvPolynomial ℕ ℤ :=
  ∏ q : Quotient p,
    MvPolynomial.X (Fintype.card {v : V // Quotient.mk' v = q})

/-- Stanley's U-polynomial, defined by deleting every subset of the edge set. -/
def stanleyU {V : Type} [Fintype V] (T : SimpleGraph V) : MvPolynomial ℕ ℤ :=
  (Finset.univ : Finset (TreeEdgeSubset T)).sum
    (fun S => componentMonomial (partitionFromCut T S))

/-- The component-degree Euler operator on the polynomial ring. -/
def componentEuler (p : MvPolynomial ℕ ℤ) : MvPolynomial ℕ ℤ :=
  (MvPolynomial.support p).sum (fun m =>
    (m.sum (fun _ e => (e : ℤ))) •
      MvPolynomial.monomial m (MvPolynomial.coeff m p))

/-- Claim 19880. -/
def claim19880 : Prop :=
  ∀ {V : Type} [Fintype V] (T : SimpleGraph V), T.IsTree →
    (graphEdges T).sum (fun e => stanleyU (T.deleteEdges {e})) =
      componentEuler (stanleyU T) - stanleyU T

/-- Claim 19881. -/
def claim19881 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W]
    (T : SimpleGraph V) (T' : SimpleGraph W),
    T.IsTree → T'.IsTree → Fintype.card V = Fintype.card W →
      (stanleyU T = stanleyU T' ↔
        (graphEdges T).sum (fun e => stanleyU (T.deleteEdges {e})) =
          (graphEdges T').sum (fun e => stanleyU (T'.deleteEdges {e})))

end

end MathlibPlus.Open.Research.TreeCuts
