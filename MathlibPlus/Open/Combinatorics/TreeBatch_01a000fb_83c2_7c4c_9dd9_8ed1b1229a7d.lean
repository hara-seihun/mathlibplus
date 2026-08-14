import Mathlib

namespace MathlibPlus.Open.Combinatorics.TreeBatch

open scoped BigOperators

/-!
The tree claims in this module use finite sets of natural-number vertex labels.
An edge is stored once, with its smaller endpoint first.  The component
partition below is the literal partition induced by a retained edge set.
-/

def edgeRelation (F : Finset (Nat × Nat)) (u v : Nat) : Prop :=
  (u, v) ∈ F ∨ (v, u) ∈ F

def connectedBy (F : Finset (Nat × Nat)) (u v : Nat) : Prop :=
  Relation.ReflTransGen (edgeRelation F) u v

noncomputable def componentVertices (V : Finset Nat) (F : Finset (Nat × Nat)) (u : Nat) :
    Finset Nat := by
  classical
  exact V.filter (fun v => connectedBy F u v)

noncomputable def componentSize (V : Finset Nat) (F : Finset (Nat × Nat)) (u : Nat) : Nat :=
  (componentVertices V F u).card

noncomputable def componentRoots (V : Finset Nat) (F : Finset (Nat × Nat)) : Finset Nat := by
  classical
  exact V.filter (fun u => ∀ v ∈ V, connectedBy F u v → u ≤ v)

noncomputable def forestMonomial (V : Finset Nat) (F : Finset (Nat × Nat)) :
    MvPolynomial Nat ℚ := by
  classical
  exact ∏ u ∈ componentRoots V F, MvPolynomial.X (componentSize V F u)

noncomputable def forestPolynomial (V : Finset Nat) (edges : Finset (Nat × Nat)) :
    MvPolynomial Nat ℚ := by
  classical
  exact ∑ F ∈ edges.powerset, forestMonomial V F

/-- A concrete finite simple tree encoding. -/
def IsFiniteTree (V : Finset Nat) (E : Finset (Nat × Nat)) : Prop :=
  (∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V ∧ e.1 < e.2) ∧
    (∀ u ∈ V, ∀ v ∈ V, connectedBy E u v) ∧ E.card + 1 = V.card

structure FiniteTree where
  vertices : Finset Nat
  edges : Finset (Nat × Nat)
  is_tree : IsFiniteTree vertices edges

noncomputable def finiteTreePolynomial (T : FiniteTree) : MvPolynomial Nat ℚ :=
  forestPolynomial T.vertices T.edges

noncomputable def splitForEdge (T : FiniteTree) (e : Nat × Nat) : Nat × Nat := by
  classical
  let F := T.edges.erase e
  let a := componentSize T.vertices F e.1
  let b := componentSize T.vertices F e.2
  exact (min a b, max a b)

noncomputable def splitProfile (T : FiniteTree) : Multiset (Nat × Nat) := by
  classical
  exact T.edges.1.map (splitForEdge T)

/-- The coefficient formulation of the split-profile claim. -/
def claim_57630 : Prop :=
  ∀ (T : FiniteTree) (a b : Nat),
    MvPolynomial.coeff
        (Finsupp.single a 1 + Finsupp.single b 1)
        (finiteTreePolynomial T) =
      (splitProfile T).count (min a b, max a b)

inductive RTree where
  | node (children : List RTree) : RTree

def RTree.size : RTree → Nat
  | .node cs => 1 + cs.foldl (fun n t => n + t.size) 0

mutual
  def edgeSet : RTree → Nat → Finset (Nat × Nat)
    | .node cs, o => edgeSetChildren o cs (o + 1)
  def edgeSetChildren : Nat → List RTree → Nat → Finset (Nat × Nat)
    | _, [], _ => ∅
    | parent, c :: cs, off =>
      {(parent, off)} ∪ edgeSet c off ∪ edgeSetChildren parent cs (off + c.size)
end

def vertexSet (t : RTree) (offset : Nat) : Finset Nat :=
  (Finset.range t.size).image (fun n => offset + n)

noncomputable def rootedTreePolynomial (t : RTree) : MvPolynomial Nat ℚ :=
  forestPolynomial (vertexSet t 0) (edgeSet t 0)

def rootedTreePredicate (t : RTree) : Prop :=
  IsFiniteTree (vertexSet t 0) (edgeSet t 0)

def treeAdj (t : RTree) (u v : Fin t.size) : Prop :=
  (u.1, v.1) ∈ edgeSet t 0 ∨ (v.1, u.1) ∈ edgeSet t 0

def treeGraphIso (s t : RTree) : Prop :=
  ∃ e : Fin s.size ≃ Fin t.size,
    ∀ u v, treeAdj s u v ↔ treeAdj t (e u) (e v)

def leaf : RTree := .node []

def r1 : RTree :=
  .node [
    .node [.node [leaf, .node [.node [leaf]]]],
    .node [.node [.node [leaf]]]
  ]

def r2 : RTree :=
  .node [
    .node [.node [leaf]],
    .node [.node [.node [leaf, .node [.node [leaf]]]]]
  ]

def r3 : RTree :=
  .node [
    leaf,
    .node [.node [.node [.node [.node [leaf, .node [.node [leaf]]]]]]]
  ]

def r4 : RTree :=
  .node [
    leaf,
    .node [.node [leaf, .node [.node [.node [.node [.node [leaf]]]]]]]
  ]

/-- The tuple spellings are, in order, the four packet rootings R₁,...,R₄. -/
def rooting : Fin 4 → RTree
  | ⟨0, _⟩ => r1
  | ⟨1, _⟩ => r2
  | ⟨2, _⟩ => r3
  | ⟨_, _⟩ => r4

def attachAtRoot (t p : RTree) : RTree :=
  match t with
  | .node cs => .node (cs ++ [p])

def path3 : RTree := .node [.node [leaf]]

def D (i : Fin 4) : RTree := attachAtRoot (rooting i) path3

def oneLeafOldRoot (i : Fin 4) : RTree := attachAtRoot (rooting i) leaf

def oneLeafNewRoot (i : Fin 4) : RTree := .node [rooting i]

def parentTree (i j : Fin 4) : RTree :=
  .node [oneLeafOldRoot i, oneLeafNewRoot j]

def p12 : RTree := parentTree 0 1
def p21 : RTree := parentTree 1 0
def p34 : RTree := parentTree 2 3
def p43 : RTree := parentTree 3 2

def namedParent : Fin 4 → RTree
  | ⟨0, _⟩ => p12
  | ⟨1, _⟩ => p21
  | ⟨2, _⟩ => p34
  | ⟨_, _⟩ => p43

def everyThreeIndependent (v : Fin 4 → MvPolynomial Nat ℚ) : Prop :=
  ∀ s : Finset (Fin 4), s.card = 3 →
    LinearIndependent ℚ (fun i : {i // i ∈ s} => v i.1)

def fourTermRelation (v : Fin 4 → MvPolynomial Nat ℚ) : Prop :=
  v 0 - v 1 + v 2 - v 3 = 0

def hRootingCondition : Prop :=
  RTree.size r1 = 11 ∧
    rootedTreePredicate r1 ∧
    ∀ i : Fin 4,
      RTree.size (rooting i) = 11 ∧ treeGraphIso r1 (rooting i)

def claim_57608 : Prop :=
  hRootingCondition ∧
    (∀ i : Fin 4, RTree.size (D i) = 14 ∧ rootedTreePredicate (D i)) ∧
    fourTermRelation (fun i => rootedTreePolynomial (D i)) ∧
    everyThreeIndependent (fun i => rootedTreePolynomial (D i))

def twoRootBranchesOfSize12 (t : RTree) : Prop :=
  match t with
  | .node [a, b] => RTree.size a = 12 ∧ RTree.size b = 12
  | _ => False

noncomputable def deleteVertexEdges (E : Finset (Nat × Nat)) (v : Nat) :
    Finset (Nat × Nat) := by
  classical
  exact E.filter (fun e => e.1 ≠ v ∧ e.2 ≠ v)

noncomputable def componentSizeAfterDelete (V : Finset Nat)
    (E : Finset (Nat × Nat)) (v u : Nat) : Nat := by
  classical
  exact ((V.erase v).filter (connectedBy (deleteVertexEdges E v) u)).card

def isCentroid (V : Finset Nat) (E : Finset (Nat × Nat)) (v : Nat) : Prop :=
  v ∈ V ∧ ∀ u ∈ V, u ≠ v →
    2 * componentSizeAfterDelete V E v u ≤ V.card

def rootIsUniqueCentroid (t : RTree) : Prop :=
  isCentroid (vertexSet t 0) (edgeSet t 0) 0 ∧
    ∀ v ∈ vertexSet t 0, isCentroid (vertexSet t 0) (edgeSet t 0) v → v = 0

def fourParentsPairwiseNonisomorphic : Prop :=
  ∀ {i j : Fin 4}, i ≠ j → ¬ treeGraphIso (namedParent i) (namedParent j)

def claim_57610 : Prop :=
  (∀ i : Fin 4,
    RTree.size (namedParent i) = 25 ∧
      rootedTreePredicate (namedParent i) ∧
      twoRootBranchesOfSize12 (namedParent i) ∧
      rootIsUniqueCentroid (namedParent i)) ∧
    fourParentsPairwiseNonisomorphic ∧
    fourTermRelation (fun i => rootedTreePolynomial (namedParent i)) ∧
    everyThreeIndependent (fun i => rootedTreePolynomial (namedParent i)) ∧
    rootedTreePolynomial p12 ≠ rootedTreePolynomial p21 ∧
    rootedTreePolynomial p34 ≠ rootedTreePolynomial p43 ∧
    rootedTreePolynomial p12 - rootedTreePolynomial p21 =
      rootedTreePolynomial r1 *
        (rootedTreePolynomial (D 0) - rootedTreePolynomial (D 1)) ∧
    rootedTreePolynomial p34 - rootedTreePolynomial p43 =
      rootedTreePolynomial r1 *
        (rootedTreePolynomial (D 2) - rootedTreePolynomial (D 3))

noncomputable def formalPartialDerivative (k : Nat)
    (p : MvPolynomial Nat ℚ) : MvPolynomial Nat ℚ := by
  classical
  exact ∑ m ∈ p.support,
    MvPolynomial.monomial (m - Finsupp.single k 1)
      (MvPolynomial.coeff m p * (m k : ℚ))

noncomputable def M (t : RTree) : MvPolynomial Nat ℚ :=
  formalPartialDerivative 1 (rootedTreePolynomial t)

noncomputable def E (k : Nat) (t : RTree) : MvPolynomial Nat ℚ :=
  formalPartialDerivative k (M t)

def claim_57613 : Prop :=
  fourTermRelation (fun i => M (namedParent i)) ∧
    (∀ k : Nat, 1 ≤ k → k ≤ 24 →
      E k p12 - E k p21 + E k p34 - E k p43 = 0) ∧
    M p12 ≠ M p21 ∧ M p34 ≠ M p43

end MathlibPlus.Open.Combinatorics.TreeBatch
