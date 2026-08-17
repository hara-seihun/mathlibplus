import MathlibPlus.Open.Combinatorics.AdmittedBatch49111TreePolynomials
import MathlibPlus.Open.Combinatorics.DTreeUPolynomial
import MathlibPlus.Open.Research.TreeReroot

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization.R2790

noncomputable section

abbrev RootedBranch := MathlibPlus.Open.Research.TreeReroot.RootedTree
abbrev BranchList := List RootedBranch
abbrev BranchMultiset := Multiset RootedBranch

abbrev BranchVertex (branches : BranchList) :=
  Σ i : Fin branches.length, Fin (branches.get i).n

abbrev NodeVertex (branches : BranchList) := Option (BranchVertex branches)

/-- The internal edge relation retains the branch occurrence index, so equal
rooted branches remain distinct vertices. -/
def sameBranchAdj (branches : BranchList)
    (x y : BranchVertex branches) : Prop :=
  ∃ h : x.1 = y.1,
    (branches.get x.1).graph.Adj x.2 (h ▸ y.2)

def nodeRelation (branches : BranchList)
    (x y : NodeVertex branches) : Prop :=
  match x, y with
  | none, none => False
  | none, some q => q.2 = (branches.get q.1).root
  | some q, none => q.2 = (branches.get q.1).root
  | some q, some r => sameBranchAdj branches q r

/-- `Node(M)`, with `none` as the displayed centroid and one dependent
occurrence carrier for each rooted branch. -/
def nodeGraph (branches : BranchList) : SimpleGraph (NodeVertex branches) :=
  SimpleGraph.fromRel (nodeRelation branches)

def nodeCandidate (branches : BranchList) : Prop :=
  (nodeGraph branches).IsTree ∧
    MathlibPlus.Open.Combinatorics.DTreeUPolynomial.centroidVertex
      (nodeGraph branches) none

abbrev TreePolynomial := Polynomial ℚ

def branchA (R : RootedBranch) (u v : TreePolynomial) : TreePolynomial :=
  ∑ S : Finset (Fin R.n),
    if MathlibPlus.Open.Combinatorics.AdmittedBatch49111.connectedSubset
          R.graph S ∧ R.root ∈ S then
      u ^ (S.card - 1) * v ^
        MathlibPlus.Open.Combinatorics.AdmittedBatch49111.edgeBoundary R.graph S
    else 0

def branchB (R : RootedBranch) (u v : TreePolynomial) : TreePolynomial :=
  v + u * branchA R u v

def branchK (R : RootedBranch) (u v : TreePolynomial) : TreePolynomial :=
  MathlibPlus.Open.Combinatorics.AdmittedBatch49111.UPolynomial R.graph u v +
    (v - 1) * branchA R u v

def branchProduct (M : BranchMultiset) (u v : TreePolynomial) : TreePolynomial :=
  Multiset.prod (M.map (fun R => branchB R u v))

def branchSum (M : BranchMultiset) (u v : TreePolynomial) : TreePolynomial :=
  Multiset.sum (M.map (fun R => branchK R u v))

def nodeU (branches : BranchList) (u v : TreePolynomial) : TreePolynomial :=
  MathlibPlus.Open.Combinatorics.AdmittedBatch49111.UPolynomial
    (nodeGraph branches) u v

/-- A candidate is minimum among displayed centroid trees having the same
connected-subtree valuation. -/
def minimumEqualUCandidate (branches : BranchList)
    (u v : TreePolynomial) : Prop :=
  nodeCandidate branches ∧
    ∀ other : BranchList,
      nodeCandidate other →
      nodeU other u v = nodeU branches u v →
      Fintype.card (NodeVertex branches) ≤ Fintype.card (NodeVertex other)

/-- Claim R-2790.2: the connected-subtree valuation decomposes at the
 displayed centroid into the containing-centroid product and branch-local
 corrections, with branch occurrences retained. -/
def claim45165 : Prop :=
  ∀ (branches : BranchList) (u v : TreePolynomial),
    nodeCandidate branches →
    nodeU branches u v =
      branchProduct (Multiset.ofList branches) u v +
        branchSum (Multiset.ofList branches) u v

/-- Claim R-2790.3: after the common occurrence multiset is cancelled from
 two minimum-order equal-valuation candidates, the exact residual equation
 remains. -/
def claim45166 : Prop :=
  ∀ (C E F : BranchList) (u v : TreePolynomial),
    minimumEqualUCandidate (C ++ E) u v →
    minimumEqualUCandidate (C ++ F) u v →
    nodeU (C ++ E) u v = nodeU (C ++ F) u v →
    branchProduct (Multiset.ofList C) u v *
        (branchProduct (Multiset.ofList E) u v -
          branchProduct (Multiset.ofList F) u v) =
      branchSum (Multiset.ofList F) u v - branchSum (Multiset.ofList E) u v

end

end MathlibPlus.Open.ResearchFormalization.R2790
