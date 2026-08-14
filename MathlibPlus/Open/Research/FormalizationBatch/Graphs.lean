import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch

open scoped Classical BigOperators

noncomputable section

/-- Connectivity of the induced graph on a nonempty vertex set. -/
def inducedConnected {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  S.Nonempty ∧
    ∀ x y : S, (SimpleGraph.induce S G).Reachable x y

/-- The finite graph-theoretic degree used for the tree predicates. -/
def vertexDegree {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) : ℕ :=
  Set.ncard (G.neighborSet v)

/-- A leaf is a vertex with exactly one neighbor. -/
def isLeaf {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) : Prop :=
  vertexDegree G v = 1

/-- A two-element finset is a pendant length-two pair precisely when one
member is a leaf adjacent to a degree-two member. -/
def pendantLengthTwoPair {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) : Prop :=
  S.card = 2 ∧
    ∃ u ∈ S, ∃ v ∈ S,
      u ≠ v ∧ G.Adj u v ∧
        ((isLeaf G u ∧ vertexDegree G v = 2) ∨
          (isLeaf G v ∧ vertexDegree G u = 2))

/-- The complement of an ordered pair of deleted vertices, viewed as an
induced graph. The pair is unordered mathematically because the predicate is
symmetric in its two arguments. -/
def deletePairLeavesConnected {V : Type*}
    (G : SimpleGraph V) (u v : V) : Prop :=
  inducedConnected G {x : V | x ≠ u ∧ x ≠ v}

/-- A finite connected tree of the specified order. -/
def isConnectedTreeOfOrder {V : Type*} [Fintype V]
    (M : ℕ) (G : SimpleGraph V) : Prop :=
  G.IsTree ∧ Fintype.card V = M

/-- Number of leaves. -/
def leafCount {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  (Finset.univ.filter (fun v : V => isLeaf G v)).card

/-- Number of connected induced vertex sets of a prescribed cardinality. -/
def connectedInducedCount {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) : ℕ :=
  (Finset.univ.filter
      (fun S : Finset V =>
        S.card = k ∧ inducedConnected G (S : Set V))).card

/-- Number of unordered pendant length-two pairs. -/
def pendantLengthTwoCount {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  (Finset.univ.filter (fun S : Finset V => pendantLengthTwoPair G S)).card

/-- The leaf-side formulation of the pendant-pair count. -/
def leafWithDegreeTwoNeighborCount {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  (Finset.univ.filter (fun v : V =>
    isLeaf G v ∧ ∃ w, G.Adj v w ∧ vertexDegree G w = 2)).card

/-- Claim 43309: the connected complement after deleting two distinct
vertices occurs exactly for two leaves or for a pendant length-two pair. -/
def terminalDeletionClassification : Prop :=
  ∀ (M : ℕ) (hM : 4 ≤ M) (V : Type*) [Fintype V]
    (G : SimpleGraph V),
    isConnectedTreeOfOrder M G →
    ∀ u v : V, u ≠ v →
      deletePairLeavesConnected G u v ↔
        ((isLeaf G u ∧ isLeaf G v) ∨
          pendantLengthTwoPair G ({u, v} : Finset V))

/-- Claim 43310: the terminal two-deletion count is the unordered leaf-pair
count plus the unordered pendant length-two count, with its equivalent
leaf-neighbor interpretation. -/
def terminalTwoDeletionIdentity : Prop :=
  ∀ (M : ℕ) (hM : 4 ≤ M) (V : Type*) [Fintype V]
    (G : SimpleGraph V),
    isConnectedTreeOfOrder M G →
      connectedInducedCount G (M - 2) =
          Nat.choose (leafCount G) 2 + pendantLengthTwoCount G ∧
        pendantLengthTwoCount G = leafWithDegreeTwoNeighborCount G

end

end MathlibPlus.Open.Research.FormalizationBatch
