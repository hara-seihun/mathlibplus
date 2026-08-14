import Mathlib

namespace MathlibPlus.Open.R3923

open scoped BigOperators

/-- The finite set of vertices joined to `v` in a finite simple graph. -/
def treeNeighbors {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (v : V) : Finset V :=
  Finset.univ.filter (fun w => T.Adj v w)

/-- The vertex degree used in the incident parent-edge polynomial. -/
def treeDegree {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (v : V) : ℕ :=
  (treeNeighbors T v).card

/-- The incident parent-edge boundary polynomial of a rooted finite tree. -/
noncomputable def incidentParentEdgeBoundaryPolynomial {V : Type*} [Fintype V]
    [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj] (r : V)
    (_hT : T.IsTree) : Polynomial ℤ :=
  (treeNeighbors T r).sum (fun w =>
    Polynomial.X ^ (treeDegree T r + treeDegree T w - 2))

/-- Exact formula for the incident parent-edge boundary polynomial. -/
def incidentParentEdgeBoundaryFormula : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (r : V) (hT : T.IsTree),
      incidentParentEdgeBoundaryPolynomial T r hT =
        (treeNeighbors T r).sum (fun w =>
          Polynomial.X ^ (treeDegree T r + treeDegree T w - 2))

end MathlibPlus.Open.R3923
