import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a000fa_e2fc_7c6c_beff_68ea79e87f53

/-- Equality of vertex decks through a permutation of deleted vertices and graph isomorphisms of cards. -/
def vertexDeckEqual {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  ∃ σ : Equiv.Perm (Fin n),
    ∀ v : Fin n,
      Nonempty
        (G.induce {u : Fin n | u ≠ v} ≃g
          H.induce {u : Fin n | u ≠ σ v})

/-- The number of labelled spanning subgraphs of `G` having the target graph type `T`. -/
noncomputable def spanningSubgraphCount {n : ℕ}
    (G T : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun S : SimpleGraph (Fin n) =>
    S ≤ G ∧ Nonempty (S ≃g T))).card

/--
Claim 44785: equal vertex decks do not determine every type-specific spanning-tree
count over finite graph orders; the two-vertex complete and empty graphs witness
this for target `K₂`.
-/
def claim44785 : Prop :=
  (¬ ∀ (n : ℕ) (G H T : SimpleGraph (Fin n)),
      T.IsTree → vertexDeckEqual G H →
        spanningSubgraphCount G T = spanningSubgraphCount H T) ∧
    let K₂ : SimpleGraph (Fin 2) := ⊤
    let twoK₁ : SimpleGraph (Fin 2) := ⊥
    K₂.IsTree ∧
      vertexDeckEqual K₂ twoK₁ ∧
        spanningSubgraphCount K₂ K₂ ≠ spanningSubgraphCount twoK₁ K₂

end MathlibPlus.Open.ResearchFormalizationBatch_01a000fa_e2fc_7c6c_beff_68ea79e87f53
