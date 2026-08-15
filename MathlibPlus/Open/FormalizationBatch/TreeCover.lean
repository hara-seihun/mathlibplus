import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.TreeCover

noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable
open Set

/-- Connectedness of a vertex set, expressed by paths staying in that set. -/
def connectedVertexSet {V : Type} (T : SimpleGraph V) (C : Set V) : Prop :=
  C.Nonempty ∧
    ∀ u ∈ C, ∀ v ∈ C,
      Relation.ReflTransGen
        (fun x y => T.Adj x y ∧ x ∈ C ∧ y ∈ C) u v

def exactlyTwoMembers {V A : Type} (C : A → Set V) : Prop :=
  ∀ v, ∃ a b, a ≠ b ∧ v ∈ C a ∧ v ∈ C b ∧
    ∀ c, v ∈ C c → c = a ∨ c = b

def exactlyOneEdgeMember {V A : Type}
    (T : SimpleGraph V) (C : A → Set V) : Prop :=
  ∀ ⦃u v⦄, T.Adj u v → ∃! a, u ∈ C a ∧ v ∈ C a

def exactConnected2Cover {V A : Type}
    (T : SimpleGraph V) (C : A → Set V) : Prop :=
  (∀ a, connectedVertexSet T (C a)) ∧
    exactlyTwoMembers C ∧ exactlyOneEdgeMember T C

def pairwiseIntersectsAtMostOne {V A : Type}
    (C : A → Set V) : Prop :=
  ∀ a b, a ≠ b → (C a ∩ C b).Subsingleton

/-- Claim 47012: for a tree the pairwise-intersection clause is derived from
connectedness and the exact vertex/edge cover clauses. -/
def claim47012 : Prop :=
  ∀ {V A : Type} (T : SimpleGraph V) (C : A → Set V),
    T.IsTree →
    (exactConnected2Cover T C ↔
      ((∀ a, connectedVertexSet T (C a)) ∧
        exactlyTwoMembers C ∧ exactlyOneEdgeMember T C ∧
        pairwiseIntersectsAtMostOne C))

end
end MathlibPlus.Open.FormalizationBatch.TreeCover
