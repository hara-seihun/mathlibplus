import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The mixed abelian group `C₂ × C₃³` is an ordinary undirected CI-group. -/
def c2TimesC3CubeUndirectedCI : Prop :=
  let G := ZMod 2 × (Fin 3 → ZMod 3)
  ∀ (S T : Set G),
    (0 : G) ∉ S →
    (0 : G) ∉ T →
    (∀ x, x ∈ S ↔ -x ∈ S) →
    (∀ x, x ∈ T ↔ -x ∈ T) →
    ∀ q : G ≃ G,
      (∀ x y, y - x ∈ S ↔ q y - q x ∈ T) →
      ∃ α : G ≃+ G, α '' S = T

end MathlibPlus.Open.GraphTheory
