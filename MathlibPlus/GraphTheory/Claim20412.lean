import Mathlib.Combinatorics.SimpleGraph.Maps

namespace MathlibPlus.GraphTheory.Claim20412

/-- Complementing every card preserves an isomorphism of finite vertex decks. -/
theorem complement_transports_vertexDeck
    {V : Type*} [Fintype V] (G H : SimpleGraph V)
    (h : ∃ σ : V ≃ V, ∀ v : V,
      Nonempty (G.induce ({v} : Set V)ᶜ ≃g H.induce ({σ v} : Set V)ᶜ)) :
    ∃ σ : V ≃ V, ∀ v : V,
      Nonempty ((Gᶜ).induce ({v} : Set V)ᶜ ≃g (Hᶜ).induce ({σ v} : Set V)ᶜ) := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ, fun v => ?_⟩
  obtain ⟨e⟩ := hσ v
  let e' : (G.induce ({v} : Set V)ᶜ)ᶜ ≃g
      (H.induce ({σ v} : Set V)ᶜ)ᶜ :=
    { toEquiv := e.toEquiv
      map_rel_iff' := by
        intro x y
        simp only [SimpleGraph.compl_adj]
        change
          (e x ≠ e y ∧ ¬(H.induce ({σ v} : Set V)ᶜ).Adj (e x) (e y)) ↔
            (x ≠ y ∧ ¬(G.induce ({v} : Set V)ᶜ).Adj x y)
        rw [e.map_rel_iff]
        constructor
        · rintro ⟨hne, hnot⟩
          refine ⟨?_, hnot⟩
          intro hxy
          exact hne (congrArg e.toEquiv hxy)
        · rintro ⟨hne, hnot⟩
          refine ⟨?_, hnot⟩
          intro heq
          exact hne (e.toEquiv.injective heq) }
  have hG : (Gᶜ).induce ({v} : Set V)ᶜ = (G.induce ({v} : Set V)ᶜ)ᶜ := by
    ext x y
    simp only [SimpleGraph.induce_adj, SimpleGraph.compl_adj]
    rw [Subtype.coe_injective.ne_iff]
  have hH : (Hᶜ).induce ({σ v} : Set V)ᶜ =
      (H.induce ({σ v} : Set V)ᶜ)ᶜ := by
    ext x y
    simp only [SimpleGraph.induce_adj, SimpleGraph.compl_adj]
    rw [Subtype.coe_injective.ne_iff]
  exact ⟨hG ▸ hH ▸ e'⟩

end MathlibPlus.GraphTheory.Claim20412
