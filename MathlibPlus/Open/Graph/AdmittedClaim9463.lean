import Mathlib

namespace MathlibPlus.Open.Graph.AdmittedClaim9463

/-- The edge-star of a vertex in a finite simple graph. -/
noncomputable def edgeStar {V : Type*} [Fintype V] [DecidableEq V]
    (Y : SimpleGraph V) [DecidableRel Y.Adj] (v : V) : Finset (Sym2 V) :=
  Y.edgeFinset.filter (fun e => v ∈ e)

/-- A vertex is missed by an edge part when no part-edge is incident with it. -/
def missesVertex {V : Type*} (A : Finset (Sym2 V)) (v : V) : Prop :=
  ∀ e ∈ A, v ∉ e

/-- Validity for an edge part and its complement in a finite simple graph. -/
def validPart {V : Type*} [Fintype V] [DecidableEq V]
    (Y : SimpleGraph V) [DecidableRel Y.Adj] (A : Finset (Sym2 V)) : Prop :=
  A ⊆ Y.edgeFinset ∧
    (∃ u : V, missesVertex A u) ∧
    (∃ w : V, missesVertex (Y.edgeFinset \ A) w)

/--
The minimum-degree floor for a valid edge part: if its complement misses a
vertex, the part contains that vertex's full edge-star, with the resulting
cardinality bounds and equality case.
-/
def minimumDegreeFloor {V : Type*} [Fintype V] [DecidableEq V]
    (Y : SimpleGraph V) [DecidableRel Y.Adj] : Prop :=
  ∀ (A : Finset (Sym2 V)) (v : V),
    validPart Y A →
    missesVertex (Y.edgeFinset \ A) v →
      edgeStar Y v ⊆ A ∧
        A.card ≥ Y.degree v ∧
        Y.degree v ≥ Y.minDegree ∧
        (A.card = Y.minDegree →
          A = edgeStar Y v ∧ Y.degree v = Y.minDegree)

end MathlibPlus.Open.Graph.AdmittedClaim9463
