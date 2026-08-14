import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

abbrev Vertex11 := Fin 11
abbrev EdgeSet11 := Finset (Nat × Nat)

/-- Undirected adjacency for the explicitly listed, canonically oriented edges. -/
def adjacent (edges : EdgeSet11) (u v : Vertex11) : Prop :=
  (u.val, v.val) ∈ edges ∨ (v.val, u.val) ∈ edges

/-- A walk encoded by a nonempty list of vertices. -/
def walkEdges (edges : EdgeSet11) : List Vertex11 → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => adjacent edges u v ∧ walkEdges edges (v :: rest)

/-- Existence of a walk with at most the indicated number of edges. -/
def walkAtMost (edges : EdgeSet11) (u v : Vertex11) (numberOfEdges : Nat) : Prop :=
  ∃ path : List Vertex11,
    path ≠ [] ∧
      path.head? = some u ∧
      path.reverse.head? = some v ∧
      path.length ≤ numberOfEdges + 1 ∧
      walkEdges edges path

/-- Isomorphism of the two explicit simple graphs on the fixed vertex set. -/
def graphIso (edges₁ edges₂ : EdgeSet11) : Prop :=
  ∃ e : Equiv.Perm Vertex11,
    ∀ u v : Vertex11,
      adjacent edges₁ u v ↔ adjacent edges₂ (e u) (e v)

/-- Degree of a vertex in an explicit graph. -/
noncomputable def degreeOf (edges : EdgeSet11) (v : Vertex11) : Nat := by
  classical
  exact (Finset.univ.filter (fun w : Vertex11 => adjacent edges v w)).card

/-- Degree multiset of an explicit graph on eleven vertices. -/
noncomputable def degreeMultiset (edges : EdgeSet11) : Multiset Nat :=
  (Finset.univ : Finset Vertex11).val.map (fun v =>
    degreeOf edges v)

/-- Connected, loop-free, ten-edge graphs on eleven vertices, i.e. the tree
condition used for the two displayed edge sets. -/
def isTree (edges : EdgeSet11) : Prop :=
  (∀ edge ∈ edges, edge.1 < 11 ∧ edge.2 < 11 ∧ edge.1 < edge.2) ∧
    (∀ u v : Vertex11, walkAtMost edges u v 10) ∧
    edges.card = 10

/-- The diameter is six, expressed by bounded walks on the explicit finite graph. -/
def hasDiameterSix (edges : EdgeSet11) : Prop :=
  (∀ u v : Vertex11, walkAtMost edges u v 6) ∧
    ∃ u v : Vertex11, ¬ walkAtMost edges u v 5

/-- Edge set `T` from Claim 19846. -/
def treeAEdges : EdgeSet11 :=
  {(0, 1), (0, 7), (1, 2), (1, 5), (1, 6), (2, 3), (2, 4),
   (7, 8), (7, 10), (8, 9)}

/-- Edge set `T'` from Claim 19846. -/
def treeBEdges : EdgeSet11 :=
  {(0, 1), (0, 5), (0, 10), (1, 2), (2, 3), (2, 4),
   (5, 6), (5, 8), (5, 9), (6, 7)}

/-- The two displayed trees have the distinct graph data asserted in Claim 19847. -/
def claim_19847 : Prop :=
  isTree treeAEdges ∧
    isTree treeBEdges ∧
    ¬ graphIso treeAEdges treeBEdges ∧
    degreeMultiset treeAEdges =
      Multiset.ofList [4, 3, 3, 2, 2, 1, 1, 1, 1, 1, 1] ∧
    degreeMultiset treeBEdges =
      Multiset.ofList [4, 3, 3, 2, 2, 1, 1, 1, 1, 1, 1] ∧
    hasDiameterSix treeAEdges ∧
    hasDiameterSix treeBEdges

end MathlibPlus.Open.ResearchFormalization
