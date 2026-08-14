import Mathlib

namespace MathlibPlus.Open.TwoSetStars

abbrev TwoSet (V : Type*) [DecidableEq V] :=
  {e : Finset V // e.card = 2}

def mapTwoSet {V W : Type*} [DecidableEq V] [DecidableEq W]
    (σ : V ≃ W) (e : TwoSet V) : TwoSet W :=
  ⟨e.1.map σ.toEmbedding, by simpa using e.2⟩

def twoSetIntersectionCard {V : Type*} [DecidableEq V]
    (e f : TwoSet V) : ℕ := (e.1 ∩ f.1).card

def vertexStar {V : Type*} [Fintype V] [DecidableEq V]
    (x : V) : Finset (TwoSet V) :=
  Finset.univ.filter (fun e => x ∈ e.1)

def starImage {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (T : TwoSet V ≃ TwoSet W) (x : V) : Finset (TwoSet W) :=
  (vertexStar x).image T

def twoSetStarReconstruction : Prop :=
  ∀ {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W],
    3 ≤ Fintype.card V → Fintype.card V = Fintype.card W →
    ∀ (T : TwoSet V ≃ TwoSet W),
    (∀ e f : TwoSet V,
      twoSetIntersectionCard e f = twoSetIntersectionCard (T e) (T f)) →
    (∀ x : V, ∃ y : W, starImage T x = vertexStar y) →
    ∃! σ : V ≃ W, ∀ e : TwoSet V, T e = mapTwoSet σ e

end MathlibPlus.Open.TwoSetStars
