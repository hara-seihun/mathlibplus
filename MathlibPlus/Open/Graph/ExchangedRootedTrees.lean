import Mathlib

namespace MathlibPlus.Open.Graph

/-- The vertex relation used to identify each attached root with its host vertex. -/
def rootedGlueRelation {Q A B : Type} (r s : Q) (a : A) (b : B) :
    Sum Q (Sum A B) → Sum Q (Sum A B) → Prop
  | .inl q, .inr (.inl x) => q = r ∧ x = a
  | .inl q, .inr (.inr y) => q = s ∧ y = b
  | _, _ => False

/-- The disjoint union of three simple graphs on the indicated sum type. -/
def rootedDisjointGraph {Q A B : Type}
    (q : SimpleGraph Q) (u : SimpleGraph A) (v : SimpleGraph B) :
    SimpleGraph (Sum Q (Sum A B)) :=
  SimpleGraph.fromRel (fun x y =>
    match x, y with
    | .inl x, .inl y => q.Adj x y
    | .inr (.inl x), .inr (.inl y) => u.Adj x y
    | .inr (.inr x), .inr (.inr y) => v.Adj x y
    | _, _ => False)

/-- Attach two rooted graphs to two vertices by identifying the corresponding roots. -/
def rootedGlue {Q A B : Type}
    (q : SimpleGraph Q) (u : SimpleGraph A) (v : SimpleGraph B)
    (r s : Q) (a : A) (b : B) :
    SimpleGraph (Quot (rootedGlueRelation r s a b)) :=
  SimpleGraph.map (Quot.mk (rootedGlueRelation r s a b))
    (rootedDisjointGraph q u v)

/-- Exact open proposition for the orbit-sensitive rooted-tree exchange claim. -/
def exchangedRootedTreesNonisomorphic : Prop :=
  ∀ {Q A B : Type} [Finite Q] [Finite A] [Finite B]
    (q : SimpleGraph Q) (u : SimpleGraph A) (v : SimpleGraph B)
    (r s : Q) (a : A) (b : B),
    q.IsTree → u.IsTree → v.IsTree →
    (∀ e : u ≃g v, e.toEquiv a ≠ b) →
    ((¬ ∃ α : q ≃g q, α.toEquiv r = s) →
      ¬ Nonempty (rootedGlue q u v r s a b ≃g rootedGlue q v u r s b a)) ∧
    ((Nonempty (rootedGlue q u v r s a b ≃g rootedGlue q v u r s b a)) →
      ∃ α : q ≃g q, α.toEquiv r = s)

end MathlibPlus.Open.Graph
