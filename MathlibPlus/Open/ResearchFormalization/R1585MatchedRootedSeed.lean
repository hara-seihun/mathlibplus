import MathlibPlus.Open.ResearchFormalization.R1585CrossRootSuspension

namespace MathlibPlus.Open.ResearchFormalization.R1585CrossRootSuspension

open Classical
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable section

/-- Connected induced vertex sets of a prescribed cardinality in a rooted-tree carrier. -/
def connectedSubtreeSets (R : RootedTree) (k : ℕ) : Finset (Finset (Fin (RootedTree.order R))) :=
  (Finset.univ : Finset (Finset (Fin (RootedTree.order R)))).filter
    (fun S => S.card = k ∧
      ((underlyingGraph R).induce (↑S : Set (Fin (RootedTree.order R)))).Connected)

/-- The ordinary connected-subtree size count at cardinality `k`. -/
def connectedSubtreeSizeCount (R : RootedTree) (k : ℕ) : ℕ :=
  (connectedSubtreeSets R k).card

/-- Connected induced vertex sets of a prescribed cardinality that contain the supplied root. -/
def rootedConnectedSubtreeSets (R : RootedTree) (k : ℕ) : Finset (Finset (Fin (RootedTree.order R))) :=
  (Finset.univ : Finset (Finset (Fin (RootedTree.order R)))).filter
    (fun S => S.card = k ∧ rootVertex R ∈ S ∧
      ((underlyingGraph R).induce (↑S : Set (Fin (RootedTree.order R)))).Connected)

/-- The root-containing connected-subtree size count at cardinality `k`. -/
def rootedConnectedSubtreeSizeCount (R : RootedTree) (k : ℕ) : ℕ :=
  (rootedConnectedSubtreeSets R k).card

/-- The twelve coordinates of the ordinary connected-subtree size vector. -/
def connectedSubtreeSizeVector (R : RootedTree) : Fin 12 → ℕ :=
  fun i => connectedSubtreeSizeCount R (i.val + 1)

/-- The twelve coordinates of the root-containing connected-subtree size vector. -/
def rootedConnectedSubtreeSizeVector (R : RootedTree) : Fin 12 → ℕ :=
  fun i => rootedConnectedSubtreeSizeCount R (i.val + 1)

def seedOrdinaryConnectedSubtreeVector : Fin 12 → ℕ :=
  ![12, 11, 13, 15, 17, 19, 20, 19, 16, 11, 5, 1]

def seedRootedConnectedSubtreeVector : Fin 12 → ℕ :=
  ![1, 2, 4, 6, 8, 12, 16, 18, 16, 11, 5, 1]

/-- Claim 39391: the explicit order-twelve rooted seed has matching ordinary
and root-containing connected-subtree vectors but different unrooted
complete U-polynomials. -/
def claim39391_orderTwelveMatchedRootedSeed : Prop :=
  RootedTree.order seedA = 12 ∧
    RootedTree.order seedB = 12 ∧
    ¬ sameRootedHost seedA seedB ∧
    connectedSubtreeSizeVector seedA = seedOrdinaryConnectedSubtreeVector ∧
    connectedSubtreeSizeVector seedB = seedOrdinaryConnectedSubtreeVector ∧
    rootedConnectedSubtreeSizeVector seedA = seedRootedConnectedSubtreeVector ∧
    rootedConnectedSubtreeSizeVector seedB = seedRootedConnectedSubtreeVector ∧
    rootedU seedA ≠ rootedU seedB

end

end MathlibPlus.Open.ResearchFormalization.R1585CrossRootSuspension
