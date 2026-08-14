import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.GraphWedge

/-- A rooted wedge is a center together with its two-element set of neighbors. -/
def RootedWedge {V : Type*} [DecidableEq V] (C : SimpleGraph V) :=
  {w : V × Finset V //
    w.2.card = 2 ∧ ∀ u ∈ w.2, C.Adj w.1 u}

@[simp] def wedgeCenter {V : Type*} [DecidableEq V] {C : SimpleGraph V}
    (w : RootedWedge C) : V := w.1.1

@[simp] def wedgeOuter {V : Type*} [DecidableEq V] {C : SimpleGraph V}
    (w : RootedWedge C) : Finset V := w.1.2

/-- The same-center wedge-slide relation, i.e. Johnson adjacency on two-sets. -/
def sameCenterSlide {V : Type*} [DecidableEq V] {C : SimpleGraph V}
    (w z : RootedWedge C) : Prop :=
  wedgeCenter w = wedgeCenter z ∧ (wedgeOuter w ∩ wedgeOuter z).card = 1

/-- The two-element neighbor sets at a fixed center. -/
def NeighborPair {V : Type*} [DecidableEq V] (C : SimpleGraph V) (x : V) :=
  {s : Finset V // s.card = 2 ∧ ∀ u ∈ s, C.Adj x u}

/-- The rooted-wedge fiber at a fixed center. -/
def CenterFiber {V : Type*} [DecidableEq V] (C : SimpleGraph V) (x : V) :=
  {w : RootedWedge C // wedgeCenter w = x}

/-- The (S)-graph on one fixed-center fiber. -/
def fiberSlideGraph {V : Type*} [DecidableEq V] (C : SimpleGraph V) (x : V) :
    SimpleGraph (CenterFiber C x) :=
  SimpleGraph.fromRel (fun w z => sameCenterSlide w.1 z.1)

/-- The Johnson graph on the two-element neighbor sets at x. -/
def johnsonAt {V : Type*} [DecidableEq V] (C : SimpleGraph V) (x : V) :
    SimpleGraph (NeighborPair C x) :=
  SimpleGraph.fromRel (fun s t => (s.1 ∩ t.1).card = 1)

/-- Claim 22732: (S) is Johnson adjacency on the unordered neighbor pairs. -/
def claim22732 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (x : V),
    Nonempty (SimpleGraph.Iso (fiberSlideGraph C x) (johnsonAt C x))

/-- Having degree at least two, stated without introducing a degree convention. -/
def HasTwoNeighbors {V : Type*} (C : SimpleGraph V) (x : V) : Prop :=
  ∃ u v, u ≠ v ∧ C.Adj x u ∧ C.Adj x v

/-- Claim 22733: every fixed-center wedge fiber is connected by (S). -/
def claim22733 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (x : V),
    HasTwoNeighbors C x →
      ∀ (w z : RootedWedge C),
        wedgeCenter w = x → wedgeCenter z = x →
          Relation.ReflTransGen (sameCenterSlide (C := C)) w z

/-- Claim 22735: adjacent center fibers have the stated sole obstruction to a (T) move. -/
def claim22735 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (x u : V),
    C.Adj x u → HasTwoNeighbors C x → HasTwoNeighbors C u →
      (∃ v w,
        C.Adj x v ∧ C.Adj u w ∧ v ≠ u ∧ w ≠ x ∧ v ≠ w) ∨
      (∃ v,
        (∀ y, C.Adj x y ∧ y ≠ u ↔ y = v) ∧
        (∀ y, C.Adj u y ∧ y ≠ x ↔ y = v))

/-- The graph obtained from R by adjoining two mutually adjacent universal vertices. -/
def universalJoin {V : Type*} (R : SimpleGraph V) : SimpleGraph (Fin 2 ⊕ V) :=
  SimpleGraph.fromRel (fun a b =>
    match a, b with
    | Sum.inl _, Sum.inl _ => True
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
    | Sum.inr x, Sum.inr y => R.Adj x y)

/-- A vertex adjacent to every other vertex. -/
def IsUniversal {V : Type*} (G : SimpleGraph V) (v : V) : Prop :=
  ∀ w, w ≠ v → G.Adj v w

/-- The induced graph after deleting two named vertices. -/
def DeletePair {α : Type*} (a b : α) := {z : α // z ≠ a ∧ z ≠ b}

def deletedUniversalJoin {V : Type*} (R : SimpleGraph V) (a b : Fin 2 ⊕ V) :
    SimpleGraph (DeletePair a b) :=
  (universalJoin R).comap (fun z => z.1)

/-- Claim 22749: any two universal vertices can be deleted without changing the core type. -/
def claim22749 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) (a b : Fin 2 ⊕ V),
    a ≠ b →
      IsUniversal (universalJoin R) a →
        IsUniversal (universalJoin R) b →
          Nonempty (SimpleGraph.Iso (deletedUniversalJoin R a b) R)

end MathlibPlus.Open.FormalizationBatch.GraphWedge
