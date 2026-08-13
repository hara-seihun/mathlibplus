import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Every low- or complementary-high-valency undirected Cayley graph on
`C₃² × C₁₁` is CI. -/
def c3SquareCyclicElevenLowAndComplementaryValencyCI : Prop :=
  let G := (Fin 2 → ZMod 3) × ZMod 11
  ∀ (S T : Set G),
    (0 : G) ∉ S →
    (0 : G) ∉ T →
    (∀ ⦃x : G⦄, x ∈ S → -x ∈ S) →
    (∀ ⦃x : G⦄, x ∈ T → -x ∈ T) →
    (S.ncard ≤ 14 ∨ 84 ≤ S.ncard) →
    (T.ncard ≤ 14 ∨ 84 ≤ T.ncard) →
    ∀ e : G ≃ G,
      (∀ x y : G, y - x ∈ S ↔ e y - e x ∈ T) →
        ∃ α : G ≃+ G, α '' S = T

end MathlibPlus.Open.GraphTheory
