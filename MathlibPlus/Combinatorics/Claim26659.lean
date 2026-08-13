import Mathlib

namespace MathlibPlus.Combinatorics

universe u v

/-- The cardinality contradiction used in the unique-outside-generator
obstruction: a bijective join map from the lower ideal to its complement is
impossible when the lower ideal is strictly larger.  The semilattice-specific
argument that uniqueness produces this map is kept as the source-level
interface; this is its exact finite cardinal core. -/
def claim26659_cardinality_obstruction : Prop :=
  ∀ (I : Type u) (O : Type v) [Fintype I] [Fintype O],
    Fintype.card O < Fintype.card I →
      ¬ ∃ f : I → O, Function.Injective f ∧ Function.Surjective f

theorem claim26659_cardinality_obstruction_proof :
    claim26659_cardinality_obstruction := by
  intro I O _ _ hcard hex
  obtain ⟨f, hinj, hsurj⟩ := hex
  have hle : Fintype.card I ≤ Fintype.card O :=
    Fintype.card_le_of_injective f hinj
  exact (not_le_of_gt hcard) hle

end MathlibPlus.Combinatorics
