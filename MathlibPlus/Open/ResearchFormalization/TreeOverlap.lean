import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.TreeOverlap

/-- The induced subgraph on a vertex set is connected. -/
def InducedConnected {V : Type} (G : SimpleGraph V) (s : Set V) : Prop :=
  (G.induce s).Connected

/-- An induced graph is a three-vertex path when it is isomorphic to `P₃`. -/
def IsThreeVertexPath {V : Type} (G : SimpleGraph V) : Prop :=
  Nonempty (G ≃g SimpleGraph.pathGraph 3)

/-- Every finite tree of order at least five has a proper two-subtree cover
whose intersection is a three-vertex path. -/
def properP3OverlapDecomposition : Prop :=
  ∀ {V : Type} [Fintype V] (T : SimpleGraph V),
    T.IsTree → 5 ≤ Fintype.card V →
      ∃ A B : Set V,
        A ⊂ Set.univ ∧ B ⊂ Set.univ ∧
        InducedConnected T A ∧ InducedConnected T B ∧
        A ∪ B = Set.univ ∧
        IsThreeVertexPath (T.induce (A ∩ B))

end MathlibPlus.Open.ResearchFormalization.TreeOverlap
