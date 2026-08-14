import Mathlib

namespace MathlibPlus.Open

/-- An isomorphism of simple graphs, expressed by an adjacency-preserving equivalence. -/
def SimpleGraphIsomorphism {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ e : V ≃ W, ∀ v w, G.Adj v w ↔ H.Adj (e v) (e w)

/-- A two-vertex graph modulo relabelling of its vertices. -/
def twoVertexGraphSetoid : Setoid (SimpleGraph (Fin 2)) where
  r := SimpleGraphIsomorphism
  iseqv := ⟨
    by
      intro G
      exact ⟨Equiv.refl _, by simp⟩,
    by
      intro G H h
      rcases h with ⟨e, he⟩
      refine ⟨e.symm, ?_⟩
      intro v w
      simpa using (he (e.symm v) (e.symm w)).symm,
    by
      intro G H K hGH hHK
      rcases hGH with ⟨e, he⟩
      rcases hHK with ⟨f, hf⟩
      refine ⟨e.trans f, ?_⟩
      intro v w
      simpa using (he v w).trans (hf (e v) (e w))⟩

/-- The unlabelled isomorphism class of a simple graph on two vertices. -/
def UnlabelledTwoVertexGraph := Quotient twoVertexGraphSetoid

/-- The graph left after deleting `v`, represented on the canonical two-element type. -/
noncomputable def deletedGraphOnFin2
    {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V)
    (hV : Fintype.card V = 3) : SimpleGraph (Fin 2) := by
  classical
  letI : Fintype {x : V // x ≠ v} := Fintype.ofFinite _
  letI : Fintype {x : V // x = v} := Fintype.ofFinite _
  let hne : Fintype.card {x : V // x ≠ v} = 2 := by
    rw [Fintype.card_subtype_compl (fun x : V => x = v)]
    simp [hV]
  exact G.comap (fun i : Fin 2 =>
    ((Fintype.equivFin {x : V // x ≠ v}).symm
      (Fin.cast hne.symm i)).1)

/-- The multiset of unlabelled vertex-deleted subgraphs, with multiplicity. -/
noncomputable def vertexDeletedDeck
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hV : Fintype.card V = 3) : Multiset UnlabelledTwoVertexGraph :=
  (Finset.univ : Finset V).1.map (fun v =>
    Quotient.mk twoVertexGraphSetoid (deletedGraphOnFin2 G v hV))

/-- Claim 59767: three-vertex graphs are reconstructed by their unlabelled vertex-deleted decks. -/
def oliveiraThatteThreeVertexReconstruction : Prop :=
  ∀ {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (hV : Fintype.card V = 3) (hW : Fintype.card W = 3),
    vertexDeletedDeck G hV = vertexDeletedDeck H hW →
      ∃ e : V ≃ W, ∀ v w, G.Adj v w ↔ H.Adj (e v) (e w)

end MathlibPlus.Open
