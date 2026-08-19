import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- In a finite `(5,5)`-good graph, a module containing both a four-clique
and an independent four-set has no outside vertex. -/
def noOutsideVertexForLargeModule : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (M : Finset V),
    (¬ ∃ K : Finset V,
      K.card = 5 ∧
        ∀ ⦃x⦄, x ∈ K → ∀ ⦃y⦄, y ∈ K → x ≠ y → G.Adj x y) →
    (¬ ∃ I : Finset V,
      I.card = 5 ∧
        ∀ ⦃x⦄, x ∈ I → ∀ ⦃y⦄, y ∈ I → x ≠ y → ¬ G.Adj x y) →
    (∀ v, v ∉ M →
      ((∀ ⦃x⦄, x ∈ M → G.Adj v x) ∨
        (∀ ⦃x⦄, x ∈ M → ¬ G.Adj v x))) →
    (∃ K₄ : Finset V,
      K₄ ⊆ M ∧ K₄.card = 4 ∧
        ∀ ⦃x⦄, x ∈ K₄ → ∀ ⦃y⦄, y ∈ K₄ → x ≠ y → G.Adj x y) →
    (∃ I₄ : Finset V,
      I₄ ⊆ M ∧ I₄.card = 4 ∧
        ∀ ⦃x⦄, x ∈ I₄ → ∀ ⦃y⦄, y ∈ I₄ → x ≠ y → ¬ G.Adj x y) →
    ∀ v, v ∉ M → False

end MathlibPlus.Open.GraphTheory
