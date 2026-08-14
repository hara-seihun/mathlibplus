import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

abbrev F7 := ZMod 7
abbrev BipartiteVertex := Bool × F7

/-- The side-labelled adjacency relation specified by a connection subset of `F₇`. -/
def sideMarkedAdjacency (A : Set F7) (v w : BipartiteVertex) : Prop :=
  v.1 ≠ w.1 ∧
    if v.1 then v.2 - w.2 ∈ A else w.2 - v.2 ∈ A

/-- Side-preserving permutation of the two labelled copies. -/
def PreservesSides (f : Equiv.Perm BipartiteVertex) : Prop :=
  ∀ (s : Bool) (x : F7), (f (s, x)).1 = s

/-- Isomorphism of the side-marked graphs, with no fixed cyclic coordinate. -/
def SideMarkedGraphIso (A B : Set F7) (f : Equiv.Perm BipartiteVertex) : Prop :=
  PreservesSides f ∧
    ∀ v w, sideMarkedAdjacency A v w ↔ sideMarkedAdjacency B (f v) (f w)

/-- The affine image `uA+t` in `F₇`. -/
def affineImage (u : F7ˣ) (t : F7) (A : Set F7) : Set F7 :=
  {y | ∃ x, x ∈ A ∧ y = (u : F7) * x + t}

/-- Claim 43150: side-marked isomorphism is exactly affine equivalence. -/
def claim43150 : Prop :=
  ∀ A B : Set F7,
    (∃ f : Equiv.Perm BipartiteVertex, SideMarkedGraphIso A B f) ↔
      ∃ u : F7ˣ, ∃ t : F7, B = affineImage u t A

end MathlibPlus.Open.ResearchFormalizationBatch
