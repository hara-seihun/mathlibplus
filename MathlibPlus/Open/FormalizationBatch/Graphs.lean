import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.Graphs

open scoped BigOperators

/-- The disjoint union of `p` copies of a clique on `c` vertices. -/
def cliqueUnion (p c : ℕ) : SimpleGraph (Fin p × Fin c) where
  Adj x y := x.1 = y.1 ∧ x.2 ≠ y.2
  symm := ⟨by
    intro x y h
    exact ⟨h.1.symm, Ne.symm h.2⟩⟩
  loopless := ⟨by
    intro x h
    exact h.2 rfl⟩

/-- A clique on the labelled vertex set `Fin n`. -/
def completeFiniteGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y
  symm := ⟨by
    intro x y h
    exact Ne.symm h⟩
  loopless := ⟨by
    intro x h
    exact h rfl⟩

/-- Disjoint sum of two simple graphs. -/
def disjointGraphSum {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph (V ⊕ W) where
  Adj x y :=
    match x, y with
    | Sum.inl v, Sum.inl w => G.Adj v w
    | Sum.inr v, Sum.inr w => H.Adj v w
    | _, _ => False
  symm := ⟨by
    intro x y
    cases x with
    | inl x =>
      cases y with
      | inl y => exact G.symm.symm x y
      | inr y => exact id
    | inr x =>
      cases y with
      | inl y => exact id
      | inr y => exact H.symm.symm x y⟩
  loopless := ⟨by
    intro x
    cases x with
    | inl x => exact G.loopless.irrefl x
    | inr x => exact H.loopless.irrefl x⟩

/-- The graph obtained by deleting a vertex, with the usual subtype carrier. -/
def deletedGraph {V : Type} (G : SimpleGraph V) (v : V) :
    SimpleGraph {x : V // x ≠ v} :=
  G.induce {x : V | x ≠ v}

def cardGraph (p c : ℕ) : SimpleGraph ((Fin (p - 1) × Fin c) ⊕ Fin (c - 1)) :=
  disjointGraphSum (cliqueUnion (p - 1) c) (completeFiniteGraph (c - 1))

def homogeneousCopies {V : Type} (q : ℕ) (J : SimpleGraph V) :
    SimpleGraph (Fin q × V) where
  Adj x y := x.1 = y.1 ∧ J.Adj x.2 y.2
  symm := ⟨by
    intro x y h
    exact ⟨h.1.symm, J.symm.symm _ _ h.2⟩⟩
  loopless := ⟨by
    intro x h
    exact J.loopless.irrefl _ h.2⟩

def deleteSet {V : Type} (v : V) : Set V := {x | x ≠ v}

def graphComponent {V : Type} (G : SimpleGraph V) (s : Set V)
    (x : V) (hx : x ∈ s) : Set V :=
  {y | y ∈ s ∧ ∃ hy : y ∈ s,
    (G.induce s).Reachable ⟨x, hx⟩ ⟨y, hy⟩}

def IsGraphComponent {V : Type} (G : SimpleGraph V) (s C : Set V) : Prop :=
  ∃ x hx, graphComponent G s x hx = C

def deletedComponent {V : Type} (G : SimpleGraph V) (v w : V)
    (hvw : v ≠ w) : Set V :=
  graphComponent G (deleteSet v) w (hvw.symm)

def copyInDeleted {V : Type} (q : ℕ) (i : Fin q) (v : Fin q × V) :
    Set {x : Fin q × V // x ≠ v} :=
  {u | u.1.1 = i}

def twoDeletionCardSetup {V : Type} [Fintype V] (p c : ℕ)
    (X : SimpleGraph V) (v w : V) : Prop :=
  SimpleGraph.Connected X ∧ v ≠ w ∧
    Nonempty (deletedGraph X v ≃g cardGraph p c) ∧
    Nonempty (deletedGraph X w ≃g cardGraph p c)

/-- Claim 23511: every card of `p K_c` is the displayed card, and there are `pc`
vertex deletions. -/
def claim23511 : Prop :=
  ∀ p c : ℕ, 2 ≤ p → 2 ≤ c →
    (∀ v : Fin p × Fin c,
      Nonempty (deletedGraph (cliqueUnion p c) v ≃g cardGraph p c)) ∧
    Fintype.card (Fin p × Fin c) = p * c

/-- Claim 23513: copies not containing the deleted vertex remain graph-isomorphic
components. -/
def claim23513 : Prop :=
  ∀ (q : ℕ) (V : Type) [Fintype V] (J : SimpleGraph V),
    2 ≤ q → SimpleGraph.Connected J →
    ∀ (i : Fin q) (v : V) (k : Fin q), k ≠ i →
      Nonempty
        ((deletedGraph (homogeneousCopies q J) (i, v)).induce
          (copyInDeleted q k (i, v)) ≃g J) ∧
      IsGraphComponent
        (deletedGraph (homogeneousCopies q J) (i, v)) Set.univ
        (copyInDeleted q k (i, v))

/-- Claim 23514: an `A` card of a homogeneous disconnected parent makes the
unaffected copies components of `A`, and the repeated connected graph is a
clique. -/
def claim23514 : Prop :=
  ∀ (p c q : ℕ) (V : Type) [Fintype V] (J : SimpleGraph V),
    2 ≤ p → 2 ≤ c → 2 ≤ q → SimpleGraph.Connected J →
    ∀ (v : Fin q × V),
      ∀ e : deletedGraph (homogeneousCopies q J) v ≃g cardGraph p c,
        (∀ k : Fin q, k ≠ v.1 →
          IsGraphComponent (cardGraph p c) Set.univ
            (e '' copyInDeleted q k v)) ∧
        ∃ d : ℕ, Nonempty (J ≃g completeFiniteGraph d)

/-- Claim 23516: the homogeneous disconnected classification. -/
def claim23516 : Prop :=
  ∀ (p c q : ℕ) (V : Type) [Fintype V] (J : SimpleGraph V),
    2 ≤ p → 2 ≤ c → 2 ≤ q → SimpleGraph.Connected J →
    (∃ v : Fin q × V, Nonempty
      (deletedGraph (homogeneousCopies q J) v ≃g cardGraph p c)) →
    Nonempty (homogeneousCopies q J ≃g cliqueUnion p c)

/-- Claim 23517: in the connected case the two-card setup has exactly the two
components forced by the statement, and `p=2`. -/
def claim23517 : Prop :=
  ∀ (p c : ℕ) (V : Type) [Fintype V] (X : SimpleGraph V) (v w : V),
    2 ≤ p → 2 ≤ c →
    (hsetup : twoDeletionCardSetup p c X v w) →
      p = 2 ∧
      let C := deletedComponent X v w hsetup.2.1
      IsGraphComponent X (deleteSet v) C ∧
      w ∈ C ∧
      ∃ D : Set V,
        IsGraphComponent X (deleteSet v) D ∧ D ≠ C ∧
          ∀ E : Set V, IsGraphComponent X (deleteSet v) E → E = C ∨ E = D

/-- Claim 23518: the neighbourhood of `v` inside the component containing `w`
is exactly the singleton `{w}`. -/
def claim23518 : Prop :=
  ∀ (p c : ℕ) (V : Type) [Fintype V] (X : SimpleGraph V) (v w : V),
    2 ≤ p → 2 ≤ c →
    (hsetup : twoDeletionCardSetup p c X v w) →
      p = 2 →
      let C := deletedComponent X v w hsetup.2.1
      ∀ D : Set V,
        IsGraphComponent X (deleteSet v) C → w ∈ C →
        IsGraphComponent X (deleteSet v) D → D ≠ C →
        (∀ E : Set V, IsGraphComponent X (deleteSet v) E → E = C ∨ E = D) →
        {u | X.Adj v u} ∩ C = {w}

/-- The star edge set used in the sharp maximum-root row family. -/
def rootStarEdges {V : Type} (x : V) (S : Finset V) : Set (Sym2 V) :=
  {e | ∃ y ∈ S, e = s(x, y)}

/-- Claim 24962: the row construction on a labelled second card. -/
def claim24962 : Prop :=
  ∀ (r n : ℕ), 3 ≤ r → n = 2 * r + 1 →
    ∀ (V : Type) [Fintype V] [DecidableEq V],
      Fintype.card V = 2 * r →
      ∀ (x : V) (S : Finset V) (J : SimpleGraph V),
        S.card = r → x ∉ S →
        (∀ y : V, ¬ J.Adj x y) → Set.ncard J.edgeSet = r - 1 →
        let H := SimpleGraph.fromEdgeSet (J.edgeSet ∪ rootStarEdges x S)
        Set.ncard H.edgeSet = 2 * r - 1 ∧
        Set.ncard (H.neighborSet x) = r ∧
        (∀ y : V, H.Adj x y ↔ y ∈ S)

end MathlibPlus.Open.FormalizationBatch.Graphs
