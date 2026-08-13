import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Every ordinary undirected Cayley graph on `C₂² × C₃⁴` of valency at most
six is a CI-graph. -/
def c2SquareC3FourthValencyAtMostSixCI : Prop :=
  let G := (Fin 2 → ZMod 2) × (Fin 4 → ZMod 3)
  ∀ (S T : Set G),
    0 ∉ S →
    0 ∉ T →
    (∀ x, x ∈ S ↔ -x ∈ S) →
    (∀ x, x ∈ T ↔ -x ∈ T) →
    Set.ncard S ≤ 6 →
    ∀ e : G ≃ G,
      (∀ x y, y - x ∈ S ↔ e y - e x ∈ T) →
      ∃ α : G ≃+ G, α '' S = T

end MathlibPlus.Open.GraphTheory
