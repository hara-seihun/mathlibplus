import Mathlib

namespace MathlibPlus.Algebra.Claim20549

open scoped BigOperators

private lemma sum_map_perm_powersetCard
    {α R : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid R]
    (u : Finset α → R) (σ : Equiv.Perm α) (k : ℕ) :
    (∑ S ∈ Finset.powersetCard k (Finset.univ : Finset α),
      u (S.map σ.toEmbedding)) =
      ∑ S ∈ Finset.powersetCard k (Finset.univ : Finset α), u S := by
  classical
  apply Finset.sum_bij (fun S _ => S.map σ.toEmbedding)
  · intro S hS
    rw [Finset.mem_powersetCard] at hS ⊢
    exact ⟨by simp, by simpa using
      (Finset.card_map σ.toEmbedding (s := S)).trans hS.2⟩
  · intro S hS T hT h
    exact Finset.map_injective σ.toEmbedding h
  · intro T hT
    refine ⟨T.map σ.symm.toEmbedding, ?_, ?_⟩
    · rw [Finset.mem_powersetCard] at hT ⊢
      exact ⟨by simp, by simpa using
        (Finset.card_map σ.symm.toEmbedding (s := T)).trans hT.2⟩
    · ext x
      simp
  · intro S hS
    rfl

/-- The displayed three-root interaction, written as the three cardinality
layers of the nonempty subsets of `Fin 3`. -/
theorem claim20549_h3_expansion {R : Type*} [AddCommGroup R]
    (u : Finset (Fin 3) → R) :
    (∑ S ∈ Finset.powersetCard 1 (Finset.univ : Finset (Fin 3)), u S) -
        (∑ S ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin 3)), u S) +
        (∑ S ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin 3)), u S) =
      u {0} + u {1} + u {2} - u {0, 1} - u {0, 2} - u {1, 2} + u {0, 1, 2} := by
  classical
  have h1 : Finset.powersetCard 1 (Finset.univ : Finset (Fin 3)) =
      ({{0}, {1}, {2}} : Finset (Finset (Fin 3))) := by decide
  have h2 : Finset.powersetCard 2 (Finset.univ : Finset (Fin 3)) =
      ({{0, 1}, {0, 2}, {1, 2}} : Finset (Finset (Fin 3))) := by decide
  have h3 : Finset.powersetCard 3 (Finset.univ : Finset (Fin 3)) =
      ({{0, 1, 2}} : Finset (Finset (Fin 3))) := by decide
  rw [h1, h2, h3]
  have h10 : ({0} : Finset (Fin 3)) ∉
      ({{1}, {2}} : Finset (Finset (Fin 3))) := by decide
  have h11 : ({1} : Finset (Fin 3)) ∉
      ({{2}} : Finset (Finset (Fin 3))) := by decide
  have h20 : ({0, 1} : Finset (Fin 3)) ∉
      ({{0, 2}, {1, 2}} : Finset (Finset (Fin 3))) := by decide
  have h21 : ({0, 2} : Finset (Fin 3)) ∉
      ({{1, 2}} : Finset (Finset (Fin 3))) := by decide
  rw [Finset.sum_insert h10, Finset.sum_insert h11,
    Finset.sum_insert h20, Finset.sum_insert h21,
    Finset.sum_singleton, Finset.sum_singleton, Finset.sum_singleton]
  abel

/-- Claim 20549: the three-root interaction is unchanged by every relabelling
of the three ordered roots.  The action on a cell-indexed family is the map
`S ↦ S.map σ`; the preceding theorem identifies this cardinality-layer form
with the displayed `h₃` expression. -/
theorem claim20549_h3_invariant {R : Type*} [AddCommGroup R]
    (u : Finset (Fin 3) → R) (σ : Equiv.Perm (Fin 3)) :
    let h₃ : (Finset (Fin 3) → R) → R := fun u =>
      (∑ S ∈ Finset.powersetCard 1 (Finset.univ : Finset (Fin 3)), u S) -
        (∑ S ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin 3)), u S) +
        (∑ S ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin 3)), u S)
    h₃ (fun S => u (S.map σ.toEmbedding)) = h₃ u := by
  dsimp
  rw [sum_map_perm_powersetCard u σ 1,
    sum_map_perm_powersetCard u σ 2,
    sum_map_perm_powersetCard u σ 3]

end MathlibPlus.Algebra.Claim20549
