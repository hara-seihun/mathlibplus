import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

noncomputable section
open Classical

 def centroidReachable {V : Type} (T : SimpleGraph V) (v u w : V) : Prop :=
  u ≠ v ∧ w ≠ v ∧
    Relation.ReflTransGen
      (fun x y : V => x ≠ v ∧ y ≠ v ∧ T.Adj x y) u w

 def componentSizeAfterDeletion {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (v w : V) : ℕ :=
  (Finset.univ.filter (centroidReachable T v w)).card

 def centroidVertex {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (v : V) : Prop :=
  ∀ w : V, w ≠ v →
    2 * componentSizeAfterDeletion T v w ≤ Fintype.card V

 def centroidCore {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : Set V :=
  {v | centroidVertex T v}

 def inducesConnected {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (C : Finset V) : Prop :=
  ∀ ⦃u w : V⦄, u ∈ C → w ∈ C →
    Relation.ReflTransGen
      (fun x y : V => x ∈ C ∧ y ∈ C ∧ T.Adj x y) u w

/-- A connected vertex set larger than half a tree contains its centroid core. -/
def claim_20298 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (C : Finset V),
    T.IsTree → inducesConnected T C →
    2 * C.card > Fintype.card V →
    ∀ v : V, v ∈ centroidCore T → v ∈ C

end
end MathlibPlus.Open.ResearchFormalizationBatch
