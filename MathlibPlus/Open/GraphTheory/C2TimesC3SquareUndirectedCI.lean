import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The mixed abelian group `C₂ × C₃²` is an ordinary undirected CI-group. -/
def c2TimesC3SquareUndirectedCI : Prop :=
  let G := (Fin 2 → ZMod 3) × ZMod 2
  ∀ (S T : Set G),
    (0 : G) ∉ S →
    (0 : G) ∉ T →
    (∀ x, x ∈ S ↔ -x ∈ S) →
    (∀ x, x ∈ T ↔ -x ∈ T) →
    ∀ e : G ≃ G,
      (∀ x y : G, y - x ∈ S ↔ e y - e x ∈ T) →
        ∃ α : G ≃+ G, α '' S = T

end MathlibPlus.Open.GraphTheory
