import Mathlib.GroupTheory.SpecificGroups.Alternating

namespace MathlibPlus.Open.GraphTheory

/-- Every family of directed Cayley relations on the alternating group on four
points is simultaneously transportable either directly or after one global
reversal of all relation symbols. -/
def alternatingFourDirectedRelationalOrientationDichotomy : Prop :=
  let G := alternatingGroup (Fin 4)
  ∀ (ι : Type) (S T : ι → Set G) (e : G ≃ G),
    (∀ i, 1 ∉ S i) →
    (∀ i, 1 ∉ T i) →
    (∀ i x y, x⁻¹ * y ∈ S i ↔ (e x)⁻¹ * e y ∈ T i) →
      (∃ φ : G ≃* G, ∀ i, φ '' S i = T i) ∨
      (∃ φ : G ≃* G, ∀ i, φ '' ((S i)⁻¹) = T i)

end MathlibPlus.Open.GraphTheory
