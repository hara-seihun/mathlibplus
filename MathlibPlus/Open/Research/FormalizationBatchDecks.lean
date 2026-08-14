import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

noncomputable section
open Classical

abbrev DeckGraph (n : ℕ) := SimpleGraph (Fin n)

def deckEdgeFinset {n : ℕ} (G : DeckGraph n) : Finset (Sym2 (Fin n)) :=
  G.edgeSet.toFinite.toFinset

def deckDeleteEdge {n : ℕ} (G : DeckGraph n) (e : Sym2 (Fin n)) : DeckGraph n :=
  SimpleGraph.fromRel (fun v w => G.Adj v w ∧ Sym2.mk v w ≠ e)

def deckDeleteVertex {n : ℕ} (G : DeckGraph n) (v : Fin n) : DeckGraph (n - 1) :=
  let s : Finset (Fin n) := Finset.univ.erase v
  let h : s.card = n - 1 := by
    dsimp [s]
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
  let e : Fin (n - 1) ≃o (s : Type) := Finset.orderIsoOfFin s h
  SimpleGraph.comap (e : Fin (n - 1) → (s : Type))
    (SimpleGraph.induce (s : Set (Fin n)) G)

def deckDeleteVertexEdge {n : ℕ} (G : DeckGraph n) (v : Fin n)
    (e : Sym2 (Fin n)) : DeckGraph (n - 1) :=
  let s : Finset (Fin n) := Finset.univ.erase v
  let h : s.card = n - 1 := by
    dsimp [s]
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
  let iso : Fin (n - 1) ≃o (s : Type) := Finset.orderIsoOfFin s h
  SimpleGraph.comap (iso : Fin (n - 1) → (s : Type))
    (SimpleGraph.induce (s : Set (Fin n)) (deckDeleteEdge G e))

def deckIncident (v : Fin n) (e : Sym2 (Fin n)) : Prop :=
  ∃ w : Fin n, Sym2.mk v w = e

def deckNonincident (v : Fin n) (e : Sym2 (Fin n)) : Prop :=
  ¬ deckIncident v e

def deckIsoRel {n : ℕ} (G H : DeckGraph n) : Prop :=
  Nonempty (G ≃g H)

instance deckGraphSetoid (n : ℕ) : Setoid (DeckGraph n) where
  r := deckIsoRel
  iseqv :=
    { refl := by intro G; exact ⟨SimpleGraph.Iso.refl⟩
      symm := by
        intro G H h
        rcases h with ⟨f⟩
        exact ⟨f.symm⟩
      trans := by
        intro G H K h₁ h₂
        rcases h₁ with ⟨f⟩
        rcases h₂ with ⟨g⟩
        exact ⟨f.trans g⟩ }

abbrev DeckGraphClass (n : ℕ) := Quotient (deckGraphSetoid n)

def deckClass {n : ℕ} (G : DeckGraph n) : DeckGraphClass n := Quotient.mk' G

def vertexCard {n : ℕ} (G : DeckGraph n) (v : Fin n) : DeckGraphClass (n - 1) :=
  deckClass (deckDeleteVertex G v)

def edgeDeck {n : ℕ} (G : DeckGraph n) : Multiset (DeckGraphClass n) :=
  (deckEdgeFinset G).val.map (fun e => deckClass (deckDeleteEdge G e))

def vertexDeck {n : ℕ} (G : DeckGraph n) : Multiset (DeckGraphClass (n - 1)) :=
  (Finset.univ : Finset (Fin n)).val.map (vertexCard G)

def mixedCornerDeck {n : ℕ} (G : DeckGraph n) : Multiset (DeckGraphClass (n - 1)) :=
  (((Finset.univ : Finset (Fin n)).product (deckEdgeFinset G)).filter
      (fun ve => deckNonincident ve.1 ve.2)).val.map
    (fun ve => deckClass (deckDeleteVertexEdge G ve.1 ve.2))

def deckAutTrivial {n : ℕ} (C : DeckGraph n) : Prop :=
  ∀ f : C ≃g C, f.toEquiv = Equiv.refl (Fin n)

/-- The mixed-corner multiset is the multiset union of the edge decks of all
vertex cards. -/
def claim_19889 : Prop :=
  ∀ (n : ℕ) (G : DeckGraph n),
    mixedCornerDeck G = ∑ v : Fin n, edgeDeck (deckDeleteVertex G v)

/-- A unique, absent, asymmetric mixed corner glues equal vertex and edge decks. -/
def claim_19891 : Prop :=
  ∀ (n : ℕ) (G H : DeckGraph n),
    vertexDeck G = vertexDeck H → edgeDeck G = edgeDeck H →
    ∀ (v : Fin n) (e : Sym2 (Fin n)),
      e ∈ G.edgeSet → deckNonincident v e →
      let C := deckDeleteVertexEdge G v e
      Multiset.count (deckClass C) (mixedCornerDeck G) = 1 →
      (∀ w : Fin n, ¬ Nonempty (C ≃g deckDeleteVertex G w)) →
      deckAutTrivial C →
      Nonempty (G ≃g H)

/-- Every equal-bideck nonisomorphic pair has degeneracy at every mixed corner. -/
def claim_19893 : Prop :=
  ∀ (n : ℕ) (G H : DeckGraph n),
    vertexDeck G = vertexDeck H → edgeDeck G = edgeDeck H →
    ¬ Nonempty (G ≃g H) →
    ∀ (v : Fin n) (e : Sym2 (Fin n)),
      e ∈ G.edgeSet → deckNonincident v e →
      let C := deckDeleteVertexEdge G v e
      Multiset.count (deckClass C) (mixedCornerDeck G) ≠ 1 ∨
      (∃ w : Fin n, Nonempty (C ≃g deckDeleteVertex G w)) ∨
      ¬ deckAutTrivial C

end
end MathlibPlus.Open.ResearchFormalizationBatch
