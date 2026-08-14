import Mathlib

namespace MathlibPlus.GraphTheory

/-- Claim 3336: a finite simple graph is `(5,5)`-good exactly when it is
5-clique-free and its complement is 5-clique-free. -/
theorem fiveFiveGood_iff_cliqueFree_and_complementCliqueFree_claim3336
    (n : ℕ) (G : SimpleGraph (Fin n)) :
    (G.CliqueFree 5 ∧ G.IndepSetFree 5) ↔
      (G.CliqueFree 5 ∧ Gᶜ.CliqueFree 5) := by
  constructor
  · rintro ⟨hclique, hindep⟩
    refine ⟨hclique, ?_⟩
    intro s hs
    exact hindep s ((SimpleGraph.isNClique_compl G).mp hs)
  · rintro ⟨hclique, hcomplique⟩
    refine ⟨hclique, ?_⟩
    intro s hs
    exact hcomplique s ((SimpleGraph.isNClique_compl G).mpr hs)

end MathlibPlus.GraphTheory
