import Mathlib

namespace MathlibPlus.Open.Research

/-- A finite rooted tree represented by its displayed list of rooted children. -/
inductive RootedTree where
  | node (children : List RootedTree) : RootedTree

namespace RootedTree

/-- The number of vertices in a rooted tree. -/
def order : RootedTree → Nat
  | .node children => 1 + (children.map order).sum

/-- The parenthesized packet notation. -/
def listed (children : List RootedTree) : RootedTree :=
  .node children

end RootedTree

/-- The first explicit rooted-tree multiset in Claim 6681. -/
def branchMultisetA : Multiset RootedTree :=
  .ofList
    [ RootedTree.listed []
    , RootedTree.listed [RootedTree.listed []]
    , RootedTree.listed
        [ RootedTree.listed []
        , RootedTree.listed []
        , RootedTree.listed [RootedTree.listed [], RootedTree.listed []]
        ]
    , RootedTree.listed
        [ RootedTree.listed [RootedTree.listed []]
        , RootedTree.listed [RootedTree.listed [RootedTree.listed []]]
        ]
    ]

/-- The second explicit rooted-tree multiset in Claim 6681. -/
def branchMultisetB : Multiset RootedTree :=
  .ofList
    [ RootedTree.listed [RootedTree.listed [], RootedTree.listed []]
    , RootedTree.listed
        [ RootedTree.listed []
        , RootedTree.listed []
        , RootedTree.listed [RootedTree.listed [RootedTree.listed []]]
        ]
    , RootedTree.listed
        [ RootedTree.listed []
        , RootedTree.listed [RootedTree.listed []]
        , RootedTree.listed [RootedTree.listed []]
        ]
    ]

/-- Total branch weight is the sum of the orders of the rooted trees in a multiset. -/
def totalBranchWeight (branches : Multiset RootedTree) : Nat :=
  (branches.map RootedTree.order).sum

/--
Claim 6681: the two displayed rooted-tree multisets are the explicit pair, and
both have total branch weight fifteen.
-/
def explicitWeightFifteenRootedMultisetPair : Prop :=
  totalBranchWeight branchMultisetA = 15 ∧
    totalBranchWeight branchMultisetB = 15

end MathlibPlus.Open.Research
