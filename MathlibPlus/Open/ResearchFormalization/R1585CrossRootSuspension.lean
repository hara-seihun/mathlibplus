import MathlibPlus.Open.Combinatorics.DTreeUPolynomial

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1585CrossRootSuspension

noncomputable section

/-- Rooted trees are represented by their rooted child lists. -/
inductive RootedTree where
  | node (children : List RootedTree)

namespace RootedTree

mutual
  def order : RootedTree → ℕ
    | .node children => 1 + forestOrder children
  def forestOrder : List RootedTree → ℕ
    | [] => 0
    | tree :: rest => order tree + forestOrder rest
end

def children : RootedTree → List RootedTree
  | .node children => children

end RootedTree

/-- Natural labels are converted to the finite vertex carrier by reduction
of the recursive order; all labels produced by `rawEdges` are in range. -/
def vertexOf : (tree : RootedTree) → ℕ → Fin (RootedTree.order tree)
  | .node children, label => Fin.ofNat (1 + RootedTree.forestOrder children) label

mutual
  def shiftedEdges (offset : ℕ) (edges : Set (ℕ × ℕ)) : Set (ℕ × ℕ) :=
    {e | ∃ e', e' ∈ edges ∧ (e'.1 + offset, e'.2 + offset) = e}
  def rawEdges : RootedTree → Set (ℕ × ℕ)
    | .node children => childEdges children 1
  def childEdges : List RootedTree → ℕ → Set (ℕ × ℕ)
    | [], _ => ∅
    | child :: rest, offset =>
        {(0, offset)} ∪
          shiftedEdges offset (rawEdges child) ∪
          childEdges rest (offset + RootedTree.order child)
end

def treeEdgeSet (tree : RootedTree) : Set (Sym2 (Fin (RootedTree.order tree))) :=
  Set.image
    (fun edge : ℕ × ℕ => s(vertexOf tree edge.1, vertexOf tree edge.2))
    (rawEdges tree)

def underlyingGraph (tree : RootedTree) : SimpleGraph (Fin (RootedTree.order tree)) :=
  SimpleGraph.fromEdgeSet (treeEdgeSet tree)

def sameUnrootedHost (R S : RootedTree) : Prop :=
  Nonempty (underlyingGraph R ≃g underlyingGraph S)

def rootVertex (R : RootedTree) : Fin (RootedTree.order R) :=
  vertexOf R 0

def sameRootedHost (R S : RootedTree) : Prop :=
  ∃ e : underlyingGraph R ≃g underlyingGraph S,
    e (rootVertex R) = rootVertex S

abbrev UPolynomial := MvPolynomial ℕ ℤ
abbrev PruningPolynomial := Polynomial UPolynomial

def rootedU (R : RootedTree) : UPolynomial :=
  MathlibPlus.Open.Combinatorics.DTreeUPolynomial.uPolynomial (underlyingGraph R)

def wMonomial (degree : ℕ) (coefficient : UPolynomial) : PruningPolynomial :=
  Polynomial.C coefficient * Polynomial.X ^ degree

mutual
  def pruningFactor : RootedTree → PruningPolynomial
    | .node children =>
        forestPruning children +
          wMonomial (RootedTree.order (.node children))
            (rootedU (.node children))
  def forestPruning : List RootedTree → PruningPolynomial
    | [] => 1
    | tree :: rest => pruningFactor tree * forestPruning rest
end

def supportedFrom (d : ℕ) (P : PruningPolynomial) : Prop :=
  ∀ i < d, P.coeff i = 0

def hasExactFirstRow (d : ℕ) (P : PruningPolynomial) : Prop :=
  supportedFrom d P ∧ P.coeff d ≠ 0

def suspensionRoot (a : ℕ) (U : UPolynomial) (P : PruningPolynomial) : PruningPolynomial :=
  P + wMonomial a U

def crossRootDifference (a : ℕ) (U : UPolynomial)
    (leftChildren rightChildren : PruningPolynomial) : PruningPolynomial :=
  leftChildren * suspensionRoot a U rightChildren -
    rightChildren * suspensionRoot a U leftChildren

def contextualCrossRootDifference (context : PruningPolynomial)
    (a : ℕ) (U : UPolynomial)
    (leftChildren rightChildren : PruningPolynomial) : PruningPolynomial :=
  context * crossRootDifference a U leftChildren rightChildren

def contextPruning (context : List RootedTree) : PruningPolynomial :=
  forestPruning context

def contextU (context : List RootedTree) : UPolynomial :=
  context.foldr (fun tree product => rootedU tree * product) 1

def productHalfMinus (context : List RootedTree) (R S : RootedTree) : PruningPolynomial :=
  contextPruning context * forestPruning (RootedTree.children R ++ [S])

def productHalfPlus (context : List RootedTree) (R S : RootedTree) : PruningPolynomial :=
  contextPruning context * forestPruning (RootedTree.children S ++ [R])

def centroidTreeMinus (context : List RootedTree) (R S : RootedTree) : RootedTree :=
  .node (context ++ RootedTree.children R ++ [S])

def centroidTreePlus (context : List RootedTree) (R S : RootedTree) : RootedTree :=
  .node (context ++ RootedTree.children S ++ [R])

def deletedRootU (T : RootedTree) : UPolynomial :=
  MathlibPlus.Open.Combinatorics.DTreeUPolynomial.uPolynomial
    ((underlyingGraph T).induce {v : Fin (RootedTree.order T) |
      v ≠ rootVertex T})

def rootDeletionDifference (R S : RootedTree) : UPolynomial :=
  deletedRootU R - deletedRootU S

def centroidCardDifference (context : List RootedTree) (R S : RootedTree) : UPolynomial :=
  deletedRootU (centroidTreeMinus context R S) -
    deletedRootU (centroidTreePlus context R S)

def pureComponentPolynomial (P : UPolynomial) : Prop :=
  ∀ m ∈ P.support, ∀ i ∈ m.support, i = 1

def everyBranchAtMost (a : ℕ) (branches : List RootedTree) : Prop :=
  ∀ tree ∈ branches, RootedTree.order tree ≤ a

/-- The exact cross-attachment identity and first-order transfer. -/
def claim39397_crossAttachmentIdentity : Prop :=
  ∀ (R S : RootedTree) (context : List RootedTree)
    (U : UPolynomial) (d : ℕ),
    sameUnrootedHost R S →
    U = rootedU R → U = rootedU S →
    let a := RootedTree.order R
    let A := forestPruning (RootedTree.children R)
    let B := forestPruning (RootedTree.children S)
    let D := pruningFactor R - pruningFactor S
    hasExactFirstRow d D →
      pruningFactor R = A + wMonomial a U ∧
      pruningFactor S = B + wMonomial a U ∧
      forestPruning (RootedTree.children R ++ [S]) -
          forestPruning (RootedTree.children S ++ [R]) =
        wMonomial a U * D ∧
      supportedFrom (a + d)
        (contextualCrossRootDifference (contextPruning context) a U A B) ∧
      (contextualCrossRootDifference (contextPruning context) a U A B).coeff (a + d) ≠ 0

/-- Pure rows precede the first suspended discrepancy and the centroid-card
factorization uses the nonzero root-deletion top slice. -/
def claim39398_pureRowsAndCentroidCardFactorization : Prop :=
  ∀ (R S : RootedTree) (context : List RootedTree)
    (U : UPolynomial) (r d : ℕ),
    sameUnrootedHost R S →
    U = rootedU R → U = rootedU S →
    context.foldr (fun tree total => RootedTree.order tree + total) 0 = 2 * r + 2 →
    2 * r + 2 ≤ RootedTree.order R →
    2 * r + 2 ≤ d →
    let a := RootedTree.order R
    let D := pruningFactor R - pruningFactor S
    let K := rootDeletionDifference R S
    hasExactFirstRow d D →
      D.coeff (a - 1) = K ∧
      K ≠ 0 →
      everyBranchAtMost a
          (context ++ RootedTree.children R ++ [S]) ∧
      everyBranchAtMost a
          (context ++ RootedTree.children S ++ [R]) ∧
      let h := a + r + 1
      h - r = a + 1 ∧
      (∀ j, h ≤ j → j ≤ h + r →
        pureComponentPolynomial ((productHalfMinus context R S).coeff j) ∧
          pureComponentPolynomial ((productHalfPlus context R S).coeff j) ∧
          (productHalfMinus context R S).coeff j =
            (productHalfPlus context R S).coeff j) ∧
      h + r < a + d ∧
      centroidCardDifference context R S =
        contextU context * U * K ∧
      centroidCardDifference context R S ≠ 0

/-- The exact order-twelve rooted seed from the retained R-1585 record. -/
def leafTree : RootedTree := .node []

def seedA : RootedTree :=
  .node
    [ .node
        [ leafTree
        , .node [ .node [ leafTree, .node [ leafTree, leafTree ] ] ]
        ]
    , .node [ .node [ leafTree ] ]
    ]

def seedB : RootedTree :=
  .node
    [ .node [ leafTree, leafTree ]
    , .node [ .node [ leafTree, .node [ leafTree, .node [ .node [ leafTree ] ] ] ] ]
    ]

def terminalLeft : RootedTree :=
  .node (RootedTree.children seedA ++ [seedB])

def terminalRight : RootedTree :=
  .node (RootedTree.children seedB ++ [seedA])

def sixLeafContext : List RootedTree := List.replicate 6 leafTree

def profile₁₅₂₆ : Finsupp ℕ ℕ :=
  Finsupp.single 1 15 + Finsupp.single 2 1 + Finsupp.single 6 1

def profile₄₅₂₆ : Finsupp ℕ ℕ :=
  Finsupp.single 1 45 + Finsupp.single 2 1 + Finsupp.single 6 1

def terminalDifference : PruningPolynomial :=
  pruningFactor terminalLeft - pruningFactor terminalRight

def suspendedTreeMinusFor (r : ℕ) : RootedTree :=
  centroidTreeMinus (List.replicate (2 * r + 2) leafTree) terminalLeft terminalRight

def suspendedTreePlusFor (r : ℕ) : RootedTree :=
  centroidTreePlus (List.replicate (2 * r + 2) leafTree) terminalLeft terminalRight

def suspendedProductMinusFor (r : ℕ) : PruningPolynomial :=
  productHalfMinus (List.replicate (2 * r + 2) leafTree) terminalLeft terminalRight

def suspendedProductPlusFor (r : ℕ) : PruningPolynomial :=
  productHalfPlus (List.replicate (2 * r + 2) leafTree) terminalLeft terminalRight

def suspendedCardDifferenceFor (r : ℕ) : UPolynomial :=
  centroidCardDifference (List.replicate (2 * r + 2) leafTree)
    terminalLeft terminalRight

/-- The explicit depth-twelve order-54 suspension witness. -/
def claim39399_explicitDepthTwelveOrder54Witness : Prop :=
  RootedTree.order seedA = 12 ∧
    RootedTree.order seedB = 12 ∧
    sameUnrootedHost terminalLeft terminalRight ∧
    ¬ sameRootedHost terminalLeft terminalRight ∧
    RootedTree.order terminalLeft = 24 ∧
    RootedTree.order terminalRight = 24 ∧
    rootedU terminalLeft = rootedU terminalRight ∧
    hasExactFirstRow 12 terminalDifference ∧
    (terminalDifference.coeff 23).coeff profile₁₅₂₆ = 1 ∧
    RootedTree.order (suspendedTreeMinusFor 2) = 54 ∧
    RootedTree.order (suspendedTreePlusFor 2) = 54 ∧
    MathlibPlus.Open.Combinatorics.DTreeUPolynomial.unicentroidal
      (underlyingGraph (suspendedTreeMinusFor 2)) ∧
    MathlibPlus.Open.Combinatorics.DTreeUPolynomial.unicentroidal
      (underlyingGraph (suspendedTreePlusFor 2)) ∧
    ¬ sameUnrootedHost (suspendedTreeMinusFor 2) (suspendedTreePlusFor 2) ∧
    (∀ j ≤ 29,
      (suspendedProductMinusFor 2).coeff j =
        (suspendedProductPlusFor 2).coeff j) ∧
    (∀ j < 36,
      (suspendedProductMinusFor 2).coeff j =
        (suspendedProductPlusFor 2).coeff j) ∧
    (suspendedProductMinusFor 2 - suspendedProductPlusFor 2).coeff 36 ≠ 0 ∧
    (suspendedCardDifferenceFor 2).coeff profile₄₅₂₆ = 1 ∧
    (∀ r ≤ 5,
      let context := List.replicate (2 * r + 2) leafTree
      let minus := suspendedTreeMinusFor r
      let plus := suspendedTreePlusFor r
      let minusProduct := suspendedProductMinusFor r
      let plusProduct := suspendedProductPlusFor r
      RootedTree.forestOrder context = 2 * r + 2 ∧
        RootedTree.order minus = 2 * 24 + 2 * r + 2 ∧
        RootedTree.order plus = 2 * 24 + 2 * r + 2 ∧
        MathlibPlus.Open.Combinatorics.DTreeUPolynomial.unicentroidal
          (underlyingGraph minus) ∧
        MathlibPlus.Open.Combinatorics.DTreeUPolynomial.unicentroidal
          (underlyingGraph plus) ∧
        ¬ sameUnrootedHost minus plus ∧
        (∀ j, j ≤ 24 + r + 1 + r →
          minusProduct.coeff j = plusProduct.coeff j) ∧
        (∀ j < 36,
          minusProduct.coeff j = plusProduct.coeff j) ∧
        (minusProduct - plusProduct).coeff 36 ≠ 0 ∧
        suspendedCardDifferenceFor r ≠ 0)

end
end MathlibPlus.Open.ResearchFormalization.R1585CrossRootSuspension
