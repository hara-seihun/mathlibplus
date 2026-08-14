import Mathlib

namespace MathlibPlus.Open.GraphTransport

abbrev TwoSet (V : Type*) [DecidableEq V] :=
  {e : Finset V // e.card = 2}

def mapTwoSet {V W : Type*} [DecidableEq V] [DecidableEq W]
    (σ : V ≃ W) (e : TwoSet V) : TwoSet W :=
  ⟨e.1.map σ.toEmbedding, by simpa using e.2⟩

def relabelGraph {V W : Type*} (σ : V ≃ W)
    (A : SimpleGraph V) : SimpleGraph W :=
  SimpleGraph.fromRel (fun x y => A.Adj (σ.symm x) (σ.symm y))

structure DeletedCardIso {V W : Type*} [DecidableEq V] [DecidableEq W]
    (A : SimpleGraph V) (B : SimpleGraph W) (i : V) (j : W) where
  toEquiv : {x : V // x ≠ i} ≃ {y : W // y ≠ j}
  adj_iff : ∀ (x y : V) (hx : x ≠ i) (hy : y ≠ i),
    A.Adj x y ↔ B.Adj (toEquiv ⟨x, hx⟩) (toEquiv ⟨y, hy⟩)

noncomputable def transportPair {V W : Type*} [DecidableEq V] [DecidableEq W]
    {A : SimpleGraph V} {B : SimpleGraph W} {i : V} {j : W}
    (φ : DeletedCardIso A B i j) (e : TwoSet V) (he : i ∉ e.1) : TwoSet W := by
  let g : (x : ↥e.1) → {x : V // x ≠ i} := fun x =>
    ⟨(x : V), by
      intro hxi
      exact he (by simpa [hxi] using x.property)⟩
  let f : (↥e.1) ↪ W :=
    { toFun := fun x => (φ.toEquiv (g x) : W)
      inj' := by
        intro x y hxy
        exact Subtype.ext
          (congrArg (fun z : {x : V // x ≠ i} => (z : V))
            (φ.toEquiv.injective (Subtype.ext hxy))) }
  refine ⟨e.1.attach.map f, ?_⟩
  calc
    (e.1.attach.map f).card = e.1.attach.card := Finset.card_map f
    _ = e.1.card := Finset.card_attach
    _ = 2 := e.2

def cardTransportRelation {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (A : SimpleGraph V) (B : SimpleGraph W) (e : TwoSet V) (f : TwoSet W) : Prop :=
  ∃ (i : V) (j : W) (φ : DeletedCardIso A B i j)
    (he : i ∉ e.1),
    j ∉ f.1 ∧ transportPair φ e he = f

def cardTransportRelationInvariantUnderRelabelling : Prop :=
  ∀ {V V' W W' : Type*} [Fintype V] [Fintype V'] [Fintype W] [Fintype W']
    [DecidableEq V] [DecidableEq V'] [DecidableEq W] [DecidableEq W']
    (A : SimpleGraph V) (B : SimpleGraph W)
    (σ : V ≃ V') (τ : W ≃ W') (e : TwoSet V) (f : TwoSet W),
    cardTransportRelation A B e f ↔
      cardTransportRelation (relabelGraph σ A) (relabelGraph τ B)
        (mapTwoSet σ e) (mapTwoSet τ f)

end MathlibPlus.Open.GraphTransport
