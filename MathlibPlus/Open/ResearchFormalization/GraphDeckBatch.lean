import Mathlib

open scoped Classical
noncomputable section

namespace MathlibPlus.Open.ResearchFormalization

/-- The graph obtained by deleting one labelled vertex. -/
def deletedCard {V : Type*} (G : SimpleGraph V) (v : V) :
    SimpleGraph {w : V // w ≠ v} :=
  G.induce {w | w ≠ v}

/-- Equality of vertex decks as equality of multisets of card isomorphism
classes, expressed by a bijective matching of all deleted cards. -/
def vertexDeckEqual {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ σ : V ≃ W, ∀ v : V,
    Nonempty (deletedCard G v ≃g deletedCard H (σ v))

/-- The number of (not necessarily induced) subgraphs of `X` isomorphic to
`F`.  A member is a genuine `SimpleGraph.Subgraph`, so edges may be omitted. -/
noncomputable def ordinarySubgraphCount
    {U V : Type*} [Finite V]
    (F : SimpleGraph U) (X : SimpleGraph V) : ℕ :=
  Nat.card {H : X.Subgraph // Nonempty (H.coe ≃g F)}

def universalVertex {V : Type*} (G : SimpleGraph V) (v : V) : Prop :=
  ∀ w, w ≠ v → G.Adj v w

def leafVertices {V : Type*} [Fintype V] (G : SimpleGraph V) : Set V :=
  {v | G.degree v = 1}

/-- Equality of the leaf decks, again retaining multiplicities through a
bijection of the leaf labels. -/
def leafDeckEqual {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ σ : {v : V // v ∈ leafVertices G} ≃ {w : W // w ∈ leafVertices H},
    ∀ v : {v : V // v ∈ leafVertices G},
      Nonempty (deletedCard G v.1 ≃g deletedCard H (σ v).1)

/-- Claim 57724: Kelly's counting lemma for ordinary, rather than induced,
subgraphs and strict size inequality. -/
def kellyCountingLemma_claim57724 : Prop :=
  ∀ {U V W : Type*} [Fintype U] [Fintype V] [Fintype W]
    (F : SimpleGraph U) (X : SimpleGraph V) (Y : SimpleGraph W),
    Fintype.card U < Fintype.card V → vertexDeckEqual X Y →
      ordinarySubgraphCount F X = ordinarySubgraphCount F Y

/-- Claim 57732: a finite graph with a universal vertex is reconstructible from
its full vertex deck. -/
def universalVertexReconstruction_claim57732 : Prop :=
  ∀ {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W),
    (∃ v, universalVertex G v) → vertexDeckEqual G H →
      Nonempty (G ≃g H)

/-- Claim 57736: leaf-deck reconstruction of finite trees of order at least
four, with repeated leaf-card isomorphism types retained. -/
def leafDeckReconstructionOfTrees_claim57736 : Prop :=
  ∀ {V W : Type*} [Fintype V] [Fintype W]
    (T : SimpleGraph V) (U : SimpleGraph W),
    T.IsTree → U.IsTree →
      4 ≤ Fintype.card V → 4 ≤ Fintype.card W →
      leafDeckEqual T U → Nonempty (T ≃g U)

/-- Claim 57740: comparison with full-deck reconstruction for trees. -/
def fullDeckReconstructionOfTrees_claim57740 : Prop :=
  ∀ {V W : Type*} [Fintype V] [Fintype W]
    (T : SimpleGraph V) (U : SimpleGraph W),
    T.IsTree → U.IsTree → vertexDeckEqual T U →
      Nonempty (T ≃g U)

end MathlibPlus.Open.ResearchFormalization
