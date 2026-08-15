import Mathlib

noncomputable section

namespace MathlibPlus.Open.GraphReconstruction

variable {V : Type*} [Fintype V]

/-- The number of neighbours of a vertex in a finite simple graph. -/
def degree (Y : SimpleGraph V) (v : V) : Nat :=
  Nat.card {w : V // Y.Adj v w}

/-- A spanning edge subgraph misses a vertex when that vertex is incident to no selected edge. -/
def misses (A : SimpleGraph V) (v : V) : Prop :=
  ∀ w, ¬ A.Adj v w

/-- The edge subgraph consisting of the edges of `Y` incident to `v`. -/
def starSubgraph (Y : SimpleGraph V) (v : V) : SimpleGraph V :=
  { Adj := fun x y => Y.Adj x y ∧ (x = v ∨ y = v)
    symm := ⟨fun x y h => by
      rcases h.2 with hx | hy
      · exact ⟨Y.symm.symm x y h.1, Or.inr hx⟩
      · exact ⟨Y.symm.symm x y h.1, Or.inl hy⟩⟩
    loopless := ⟨fun x h => Y.loopless.irrefl x h.1⟩ }

/-- The edge subgraph `E(Y-v)`, represented on the ambient vertex type. -/
def deleteVertex (Y : SimpleGraph V) (v : V) : SimpleGraph V :=
  { Adj := fun x y => Y.Adj x y ∧ x ≠ v ∧ y ≠ v
    symm := ⟨fun x y h => ⟨Y.symm.symm x y h.1, h.2.2, h.2.1⟩⟩
    loopless := ⟨fun x h => Y.loopless.irrefl x h.1⟩ }

/-- The vertices incident to at least one edge of an edge subgraph. -/
def edgeSupport (A : SimpleGraph V) :=
  {x : V // ∃ y, A.Adj x y}

def starCenter (d : Nat) : Fin (d + 1) :=
  ⟨0, by omega⟩

/-- The graph `K_{1,d}` on its centre and `d` leaves. -/
def kOneD (d : Nat) : SimpleGraph (Fin (d + 1)) :=
  { Adj := fun x y =>
      (x = starCenter d ∧ y ≠ starCenter d) ∨
      (y = starCenter d ∧ x ≠ starCenter d)
    symm := ⟨fun x y h => by
      rcases h with ⟨hx, hy⟩ | ⟨hy, hx⟩
      · exact Or.inr ⟨hx, hy⟩
      · exact Or.inl ⟨hy, hx⟩⟩
    loopless := ⟨fun x h => by
      rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact hy hx
      · exact hy hx⟩ }

/-- An explicit graph isomorphism from the non-isolated part of `A` to `K_{1,d}`. -/
def graphIsoToKOneD (A : SimpleGraph V) (d : Nat)
    (e : edgeSupport A ≃ Fin (d + 1)) : Prop :=
  ∀ x y : edgeSupport A,
    A.Adj x.1 y.1 ↔ (kOneD d).Adj (e x) (e y)

def isomorphicToKOneD (A : SimpleGraph V) (d : Nat) : Prop :=
  ∃ e : edgeSupport A ≃ Fin (d + 1), graphIsoToKOneD A d e

/-- `v` is the distinguished centre under an explicit isomorphism to `K_{1,d}`. -/
def isKOneDCenter (A : SimpleGraph V) (d : Nat) (v : V) : Prop :=
  ∃ hv : ∃ w, A.Adj v w,
    ∃ e : edgeSupport A ≃ Fin (d + 1),
      graphIsoToKOneD A d e ∧ e ⟨v, hv⟩ = starCenter d

/-- Equality of edge subsets, independent of the ambient proof fields of `SimpleGraph`. -/
def sameEdges (A B : SimpleGraph V) : Prop :=
  ∀ x y, A.Adj x y ↔ B.Adj x y

/-- A valid complementary pair of edge subsets of `Y`. -/
def validPair (Y A B : SimpleGraph V) : Prop :=
  (∀ x y, Y.Adj x y ↔ (A.Adj x y ∨ B.Adj x y)) ∧
  (∀ x y, ¬ (A.Adj x y ∧ B.Adj x y)) ∧
  (∃ v, misses A v) ∧
  (∃ v, misses B v)

def minimumDegreeAtLeastTwo (Y : SimpleGraph V) : Prop :=
  ∀ v, 2 ≤ degree Y v

def nonUniversal (Y : SimpleGraph V) (v : V) : Prop :=
  ∃ w, w ≠ v ∧ ¬ Y.Adj v w

def starFirstPair (Y A B : SimpleGraph V) : Prop :=
  validPair Y A B ∧ ∃ d, isomorphicToKOneD A d

/--
All valid star-first complementary pairs in a finite simple graph of minimum degree at
least two are precisely the pairs obtained from non-universal vertex stars.
-/
def claim9469 : Prop :=
  ∀ (Y : SimpleGraph V),
    minimumDegreeAtLeastTwo Y →
      (∀ (A B : SimpleGraph V) (d : Nat),
        validPair Y A B →
        isomorphicToKOneD A d →
          ∃ v : V,
            isKOneDCenter A d v ∧
            (∀ w : V, misses B w → w = v) ∧
            sameEdges A (starSubgraph Y v) ∧
            d = degree Y v ∧
            sameEdges B (deleteVertex Y v) ∧
            nonUniversal Y v) ∧
      (∀ (A B : SimpleGraph V),
        starFirstPair Y A B ↔
          ∃ v : V,
            nonUniversal Y v ∧
            sameEdges A (starSubgraph Y v) ∧
            sameEdges B (deleteVertex Y v))

end MathlibPlus.Open.GraphReconstruction
