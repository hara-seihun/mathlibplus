import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The mixed abelian group `C₃² × C₅` is an ordinary undirected CI-group. -/
def c3SquareCyclicFiveUndirectedCI : Prop :=
  let G := (Fin 2 → ZMod 3) × ZMod 5
  ∀ S T : Set G,
    0 ∉ S →
    0 ∉ T →
    (∀ x, x ∈ S ↔ -x ∈ S) →
    (∀ x, x ∈ T ↔ -x ∈ T) →
    (∃ q : G ≃ G, ∀ x y : G,
      y - x ∈ S ↔ q y - q x ∈ T) →
    ∃ α : G ≃+ G, α '' S = T

end MathlibPlus.Open.GraphTheory
