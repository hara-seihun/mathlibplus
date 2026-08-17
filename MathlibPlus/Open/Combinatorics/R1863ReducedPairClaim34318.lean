import Mathlib

noncomputable section

namespace MathlibPlus.Open.Combinatorics.R1863ReducedPair

/-- The finite rooted-tree syntax used by the explicit spider family. -/
inductive ShapeTree where
  | node (children : List ShapeTree)

open ShapeTree

/-- Number of vertices in a rooted tree. -/
def rootedTreeOrder : ShapeTree → ℕ
  | node children => 1 + (children.map rootedTreeOrder).sum

/-- A path tail with the stated number of vertices. -/
def pathStarTail : ℕ → ShapeTree
  | 0 => node []
  | step + 1 => node [pathStarTail step]

def arm (length : ℕ) : ShapeTree :=
  pathStarTail (length - 1)

def reducedPositiveShape (longArm : ℕ) : ShapeTree :=
  node [arm 1, arm 1, arm longArm, arm 6]

def doubleSpiderBridge : ℕ → ShapeTree
  | 0 => node [arm 2, arm 6]
  | step + 1 => node [doubleSpiderBridge step]

def reducedNegativeShape (longArm : ℕ) : ShapeTree :=
  node [arm 1, arm 1, doubleSpiderBridge (longArm - 3)]

mutual
  /-- Maximum degree after forgetting the root. -/
  def unrootedMaximumDegree : ShapeTree → ℕ
    | node children =>
        max children.length (unrootedMaximumDegreeWithParentList children)

  /-- Maximum degree when the tree is attached to one parent vertex. -/
  def unrootedMaximumDegreeWithParent : ShapeTree → ℕ
    | node children =>
        max (children.length + 1)
          (unrootedMaximumDegreeWithParentList children)

  def unrootedMaximumDegreeWithParentList : List ShapeTree → ℕ
    | [] => 0
    | child :: children =>
        max (unrootedMaximumDegreeWithParent child)
          (unrootedMaximumDegreeWithParentList children)
end

/-- Paths in the syntax, used as the vertices of its unrooted graph. -/
def validPath : ShapeTree → List ℕ → Prop
  | node _, [] => True
  | node children, index :: rest =>
      ∃ child, children[index]? = some child ∧ validPath child rest

abbrev ShapeVertex (T : ShapeTree) := {path : List ℕ // validPath T path}

def childrenAtPath : ShapeTree → List ℕ → List ShapeTree
  | node children, [] => children
  | node children, index :: rest =>
      match children[index]? with
      | some child => childrenAtPath child rest
      | none => []

def shapeVertexDegree {T : ShapeTree} (v : ShapeVertex T) : ℕ :=
  (childrenAtPath T v.1).length + if v.1 = [] then 0 else 1

def shapeParentPath {T : ShapeTree}
    (parent child : ShapeVertex T) : Prop :=
  ∃ index : ℕ, child.1 = parent.1 ++ [index]

def shapeAdjacency (T : ShapeTree)
    (u v : ShapeVertex T) : Prop :=
  shapeParentPath u v ∨ shapeParentPath v u

/-- Unrooted graph isomorphism of the concrete rooted-tree syntax; the root is
not required to be preserved. -/
def unrootedTreeIsomorphic (A B : ShapeTree) : Prop :=
  ∃ e : ShapeVertex A ≃ ShapeVertex B,
    ∀ u v, shapeAdjacency A u v ↔ shapeAdjacency B (e u) (e v)

/-- Degree preservation is stated explicitly for the unrooted isomorphism
carrier, as used by the degree obstruction. -/
def preservesMaximumDegree (A B : ShapeTree) : Prop :=
  ∀ (e : ShapeVertex A ≃ ShapeVertex B),
    (∀ u v, shapeAdjacency A u v ↔ shapeAdjacency B (e u) (e v)) →
      unrootedMaximumDegree A = unrootedMaximumDegree B

/-- Claim 34318: the concrete reduced spider has a degree-four vertex while
the concrete double spider has maximum degree three, so the pair is not
unrootedly isomorphic. -/
def reducedPairNonisomorphic_claim34318 : Prop :=
  ∀ (longArm : ℕ), 3 ≤ longArm →
    unrootedMaximumDegree (reducedPositiveShape longArm) = 4 ∧
      unrootedMaximumDegree (reducedNegativeShape longArm) = 3 ∧
      preservesMaximumDegree
        (reducedPositiveShape longArm)
        (reducedNegativeShape longArm) ∧
      ¬unrootedTreeIsomorphic
        (reducedPositiveShape longArm)
        (reducedNegativeShape longArm)

end MathlibPlus.Open.Combinatorics.R1863ReducedPair
