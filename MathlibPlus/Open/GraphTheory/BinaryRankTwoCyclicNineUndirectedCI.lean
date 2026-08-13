import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The abelian group `C₂² × C₉` is an ordinary undirected CI-group. -/
def binaryRankTwoCyclicNineUndirectedCI : Prop :=
  let G := (Fin 2 → ZMod 2) × ZMod 9
  ∀ (S T : Set G),
    (0 : G) ∉ S →
    (0 : G) ∉ T →
    (∀ ⦃x : G⦄, x ∈ S → -x ∈ S) →
    (∀ ⦃x : G⦄, x ∈ T → -x ∈ T) →
    ∀ e : G ≃ G,
      (∀ x y : G, y - x ∈ S ↔ e y - e x ∈ T) →
        ∃ α : G ≃+ G, α '' S = T

end MathlibPlus.Open.GraphTheory
