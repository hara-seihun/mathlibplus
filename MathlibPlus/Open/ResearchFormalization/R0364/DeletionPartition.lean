import Mathlib

open Classical

namespace MathlibPlus.Open.ResearchFormalization.R0364.DeletionPartition

noncomputable section

/-- The four cells of the vertices outside an unordered pair. -/
def commonCell {V : Type*} (G : SimpleGraph V) (x y : V) : Set V :=
  {v | v ≠ x ∧ v ≠ y ∧ G.Adj x v ∧ G.Adj y v}

def leftExclusiveCell {V : Type*} (G : SimpleGraph V) (x y : V) : Set V :=
  {v | v ≠ x ∧ v ≠ y ∧ G.Adj x v ∧ ¬ G.Adj y v}

def rightExclusiveCell {V : Type*} (G : SimpleGraph V) (x y : V) : Set V :=
  {v | v ≠ x ∧ v ≠ y ∧ ¬ G.Adj x v ∧ G.Adj y v}

def neitherCell {V : Type*} (G : SimpleGraph V) (x y : V) : Set V :=
  {v | v ≠ x ∧ v ≠ y ∧ ¬ G.Adj x v ∧ ¬ G.Adj y v}

/-- The raw, unsorted data of a pair.  Sorting is applied only by p_ε. -/
def pairRawData {V : Type*} (G : SimpleGraph V) (x y : V) :
    Bool × (ℕ × (ℕ × ℕ)) :=
  (if G.Adj x y then true else false,
    (Set.ncard (G.commonNeighbors x y),
      ((G.neighborSet x \ (G.neighborSet y ∪ {y})).ncard,
        (G.neighborSet y \ (G.neighborSet x ∪ {x})).ncard)))

/-- Common-neighbour count after deleting v, with old labels retained. -/
def deletedCommonCount {V : Type*} (G : SimpleGraph V) (v x y : V) : ℕ :=
  Set.ncard {z | z ≠ v ∧ G.Adj x z ∧ G.Adj y z}

/-- First exclusive count after deleting v, with the endpoint convention retained. -/
def deletedLeftExclusiveCount {V : Type*} (G : SimpleGraph V)
    (v x y : V) : ℕ :=
  Set.ncard {z | z ≠ v ∧ z ≠ y ∧ G.Adj x z ∧ ¬ G.Adj y z}

/-- Second exclusive count after deleting v, with the endpoint convention retained. -/
def deletedRightExclusiveCount {V : Type*} (G : SimpleGraph V)
    (v x y : V) : ℕ :=
  Set.ncard {z | z ≠ v ∧ z ≠ x ∧ ¬ G.Adj x z ∧ G.Adj y z}

/-- Pair data on the card G-v, still indexed by the surviving old labels. -/
def deletedPairRawData {V : Type*} (G : SimpleGraph V) (v x y : V) :
    Bool × (ℕ × (ℕ × ℕ)) :=
  (if G.Adj x y then true else false,
    (deletedCommonCount G v x y,
      (deletedLeftExclusiveCount G v x y,
        deletedRightExclusiveCount G v x y)))

/-- A pair is present in a vertex-deleted card exactly when both endpoints survive. -/
def pairSurvivesDeletion {V : Type*} (v x y : V) : Prop :=
  v ≠ x ∧ v ≠ y

/-- The exact deletion transitions attached to the four cells. -/
def deletionCellEffects {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x y : V) : Prop :=
  (∀ v, v ∈ commonCell G x y →
    deletedPairRawData G v x y =
      (if G.Adj x y then true else false,
        (Set.ncard (G.commonNeighbors x y) - 1,
          ((G.neighborSet x \ (G.neighborSet y ∪ {y})).ncard,
            (G.neighborSet y \ (G.neighborSet x ∪ {x})).ncard)))) ∧
  (∀ v, v ∈ leftExclusiveCell G x y →
    deletedPairRawData G v x y =
      (if G.Adj x y then true else false,
        (Set.ncard (G.commonNeighbors x y),
          ((G.neighborSet x \ (G.neighborSet y ∪ {y})).ncard - 1,
            (G.neighborSet y \ (G.neighborSet x ∪ {x})).ncard)))) ∧
  (∀ v, v ∈ rightExclusiveCell G x y →
    deletedPairRawData G v x y =
      (if G.Adj x y then true else false,
        (Set.ncard (G.commonNeighbors x y),
          ((G.neighborSet x \ (G.neighborSet y ∪ {y})).ncard,
            (G.neighborSet y \ (G.neighborSet x ∪ {x})).ncard - 1)))) ∧
  (∀ v, v ∈ neitherCell G x y →
    deletedPairRawData G v x y = pairRawData G x y) ∧
  (∀ v, v = x ∨ v = y → ¬ pairSurvivesDeletion v x y)

/-- The four cells are exhaustive and pairwise disjoint. -/
def deletionCellPartition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x y : V) : Prop :=
  ({v : V | v ≠ x ∧ v ≠ y} : Set V) =
      commonCell G x y ∪ leftExclusiveCell G x y ∪
        rightExclusiveCell G x y ∪ neitherCell G x y ∧
    Disjoint (commonCell G x y) (leftExclusiveCell G x y) ∧
    Disjoint (commonCell G x y) (rightExclusiveCell G x y) ∧
    Disjoint (commonCell G x y) (neitherCell G x y) ∧
    Disjoint (leftExclusiveCell G x y) (rightExclusiveCell G x y) ∧
    Disjoint (leftExclusiveCell G x y) (neitherCell G x y) ∧
    Disjoint (rightExclusiveCell G x y) (neitherCell G x y)

/-- The admitted deletion-partition statement.  It makes no adjacency
assumption on the pair, so the same four cases cover both ε=1 and ε=0. -/
def claim20448_deletionPartitionProof : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x y : V), x ≠ y →
    deletionCellPartition G x y ∧ deletionCellEffects G x y

end
end MathlibPlus.Open.ResearchFormalization.R0364.DeletionPartition
