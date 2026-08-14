import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.RootedBoundaryLayers

noncomputable section

abbrev VPolynomial := Polynomial ℚ
abbrev BoundaryPolynomial := Polynomial VPolynomial

/-- An ordered occurrence presentation of a rooted tree.  All products and
profiles below are invariant under reordering the child list. -/
inductive RootedTree where
  | node (children : List RootedTree)

/-- The order of a rooted tree. -/
def treeOrder : RootedTree → ℕ
  | .node children => 1 + children.foldr (fun child n => treeOrder child + n) 0

def forestOrder : List RootedTree → ℕ
  | [] => 0
  | child :: children => treeOrder child + forestOrder children

def rootDegree : RootedTree → ℕ
  | .node children => children.length

/-- The two-level boundary polynomial `B_R`, with coefficients in `ℚ[v]` and
polynomial variable `z`. -/
def zVariable : BoundaryPolynomial := Polynomial.X
def vVariable : VPolynomial := Polynomial.X
def vCoefficient : BoundaryPolynomial := Polynomial.C vVariable

mutual
  def rootedBoundary : RootedTree → BoundaryPolynomial
    | .node children =>
      vCoefficient + zVariable * forestBoundary children
  def forestBoundary : List RootedTree → BoundaryPolynomial
    | [] => 1
    | child :: children => rootedBoundary child * forestBoundary children
  def rootedSubtreeProfile (W : ℕ) : RootedTree → BoundaryPolynomial
    | .node children =>
      zVariable ^ (W - treeOrder (.node children)) + forestSubtreeProfile W children
  def forestSubtreeProfile (W : ℕ) : List RootedTree → BoundaryPolynomial
    | [] => 0
    | child :: children =>
      rootedSubtreeProfile W child + forestSubtreeProfile W children
  def rootedSubtreeProfileCount (k : ℕ) : RootedTree → ℕ
    | .node children =>
      (if treeOrder (.node children) = k then 1 else 0) +
        forestSubtreeProfileCount k children
  def forestSubtreeProfileCount (k : ℕ) : List RootedTree → ℕ
    | [] => 0
    | child :: children =>
      rootedSubtreeProfileCount k child + forestSubtreeProfileCount k children
end

/-- The factor-count geometric sum occurring in the degree-one boundary layer. -/
def boundaryGeometricSum (k : ℕ) : VPolynomial :=
  Finset.sum (Finset.range k) (fun i => vVariable ^ i)

def boundaryFactorCount (F : List RootedTree) : ℕ := F.length

def closingVariable : BoundaryPolynomial :=
  Polynomial.C (1 - vVariable)

/-- Claim 40505: a nonzero degree-one secant of two rooted boundary products is
forced by their factor counts and has the displayed geometric-sum form. -/
def claim40505_degreeOneBoundaryLayer : Prop :=
  ∀ F G : List RootedTree,
    (forestBoundary F - forestBoundary G).natDegree ≤ 1 →
    (boundaryFactorCount F = boundaryFactorCount G →
      forestBoundary F = forestBoundary G) ∧
    (forestBoundary F ≠ forestBoundary G →
      ∃ ε : ℚ, (ε = 1 ∨ ε = -1) ∧
        forestBoundary F - forestBoundary G =
          Polynomial.C
              (vVariable ^ min (boundaryFactorCount F) (boundaryFactorCount G) *
                boundaryGeometricSum
                  (Nat.dist (boundaryFactorCount F) (boundaryFactorCount G)) *
                Polynomial.C ε) *
            (zVariable - closingVariable))

/-- Claim 40512: the first `v`-adic layer of a rooted-forest product records
all rooted subtree-size counts, and a sufficiently low residual `z` degree forces
agreement of the corresponding profiles. -/
def claim40512_firstVAdicLayerRecordsSubtreeSizeProfiles : Prop :=
  (∀ F : List RootedTree,
    ∃ R : BoundaryPolynomial,
      forestBoundary F =
        zVariable ^ forestOrder F + vCoefficient *
          forestSubtreeProfile (forestOrder F) F +
          vCoefficient ^ 2 * R) ∧
  (∀ F G : List RootedTree, ∀ e : ℕ,
    forestOrder F = forestOrder G →
    (forestBoundary F - forestBoundary G).natDegree ≤ e →
    ∀ k : ℕ, k < forestOrder F - e →
      forestSubtreeProfileCount k F = forestSubtreeProfileCount k G)

end

end MathlibPlus.Open.RootedBoundaryLayers
