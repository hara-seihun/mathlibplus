import MathlibPlus.Open.Combinatorics.TreeBatch_01a000fb_83c2_7c4c_9dd9_8ed1b1229a7d
import MathlibPlus.Open.Research.TreeCuts

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchR3738

noncomputable section

open MathlibPlus.Open.Combinatorics.TreeBatch
open MathlibPlus.Open.Research.TreeCuts

abbrev UPolynomial := MvPolynomial ℕ ℚ
abbrev RootedFactorPolynomial := Polynomial UPolynomial

/-- The ordinary component-size polynomial of a rooted-tree encoding after
forgetting its root designation. -/
def ordinaryUPolynomial (T : RTree) : UPolynomial :=
  rootedTreePolynomial T

/-- The component-size polynomial of the forest obtained by deleting the
implicit root vertex `0`. -/
def rootDeletedUPolynomial (T : RTree) : UPolynomial :=
  forestPolynomial
    ((vertexSet T 0).erase 0)
    (deleteVertexEdges (edgeSet T 0) 0)

mutual
  /-- A genuine rooted factor carries its root marker in the polynomial
  variable `z`; its constant part is the unrooted polynomial of the factor. -/
  def rootedFactorPolynomial : RTree → RootedFactorPolynomial
    | .node children =>
        Polynomial.C (ordinaryUPolynomial (.node children)) +
          Polynomial.X * rootedChildrenProduct children

  def rootedChildrenProduct : List RTree → RootedFactorPolynomial
    | [] => 1
    | child :: children =>
        rootedFactorPolynomial child * rootedChildrenProduct children
end

/-- The product of the genuine rooted factors at the implicit root. -/
def rootBranchProduct (T : RTree) : RootedFactorPolynomial :=
  match T with
  | .node children => rootedChildrenProduct children

/-- Root forgetting removes the marker and records its exponent as a
component-size variable. -/
def rootForgetting (P : RootedFactorPolynomial) : UPolynomial :=
  ∑ k ∈ P.support,
    MvPolynomial.X k * P.coeff k

/-- The shifted root-forgetting operators `A_j(P) = Φ(z^j P)`. -/
def shiftedRootForgetting
    (j : ℕ) (P : RootedFactorPolynomial) : UPolynomial :=
  rootForgetting (Polynomial.X ^ j * P)

def A₁ (P : RootedFactorPolynomial) : UPolynomial :=
  shiftedRootForgetting 1 P

def A₂ (P : RootedFactorPolynomial) : UPolynomial :=
  shiftedRootForgetting 2 P

def sameUnrootedHost (R S : RTree) : Prop :=
  treeGraphIso R S

/-- Claim 50257: root forgetting, the constant-marker deletion defect, and the
one-leaf extension identity for two rooted presentations of one unrooted tree. -/
def claim50257_rooted_host_leaf_extension_identities : Prop :=
  ∀ (R S : RTree),
    rootedTreePredicate R →
      rootedTreePredicate S →
        sameUnrootedHost R S →
          A₁ (rootBranchProduct R) = ordinaryUPolynomial R ∧
            A₁ (rootBranchProduct S) = ordinaryUPolynomial R ∧
            (rootBranchProduct R - rootBranchProduct S).coeff 0 =
              rootDeletedUPolynomial R - rootDeletedUPolynomial S ∧
            ordinaryUPolynomial (attachAtRoot R leaf) -
                ordinaryUPolynomial (attachAtRoot S leaf) =
              A₂ (rootBranchProduct R - rootBranchProduct S)

end

end MathlibPlus.Open.ResearchFormalization.BatchR3738
