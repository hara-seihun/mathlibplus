import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- The carrier of the two-subsets of a finite vertex carrier. -/
def twoSubsetEdges {V : Type} [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  (Finset.univ : Finset V).powerset.filter (fun e => e.card = 2)

/-- The image of an edge under one of the prescribed local permutations. -/
def permutedEdge {V : Type} [DecidableEq V]
    (σ : Equiv.Perm V) (e : Finset V) : Finset V :=
  e.image σ

/--
The bipartite constraint multigraph: an edge `(e, e')` records the multiedge
from the left vertex `A_e` to the right vertex `B_e'`.
-/
def constraintMultigraph {V : Type} [Fintype V] [DecidableEq V]
    (π : V → Equiv.Perm V) : Multiset (Finset V × Finset V) :=
  ((Finset.univ.product (twoSubsetEdges (V := V))).filter
      (fun p => p.1 ∉ p.2)).val.map
    (fun p => (p.2, permutedEdge (π p.1) p.2))

/-- The multidegree of the left vertex `A_e` in the constraint multigraph. -/
def leftVariableDegree {V : Type} [Fintype V] [DecidableEq V]
    (π : V → Equiv.Perm V) (e : Finset V) : ℕ :=
  Multiset.count e ((constraintMultigraph π).map Prod.fst)

/--
For prescribed pointed local permutations, every left variable `A_e` has one
incident constraint for each deleted vertex outside `e`, and therefore has
multidegree `n - 2`.
-/
def leftVariablesHaveDegreeNMinusTwo : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (n : ℕ),
    Fintype.card V = n →
    ∀ (π : V → Equiv.Perm V),
      (∀ i : V, π i i = i) →
      ∀ (e : Finset V),
        e.card = 2 →
        leftVariableDegree π e = n - 2

end MathlibPlus.Open.Combinatorics
