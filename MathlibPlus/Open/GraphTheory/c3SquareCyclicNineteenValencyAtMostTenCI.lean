import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Ordinary undirected CI for `C₃² × C₁₉` in the low and complementary
valency bands certified by the exhaustive atom-layer census. -/
def c3SquareCyclicNineteenValencyAtMostTenCI : Prop :=
  let G := (Fin 2 → ZMod 3) × ZMod 19
  ∀ (S T : Set G),
    (0 : G) ∉ S →
    (0 : G) ∉ T →
    (∀ x, x ∈ S ↔ -x ∈ S) →
    (∀ x, x ∈ T ↔ -x ∈ T) →
    (S.ncard ≤ 10 ∨ 160 ≤ S.ncard) →
    (T.ncard ≤ 10 ∨ 160 ≤ T.ncard) →
    ∀ e : G ≃ G,
      (∀ x y : G, y - x ∈ S ↔ e y - e x ∈ T) →
        ∃ α : G ≃+ G, α '' S = T

end MathlibPlus.Open.GraphTheory
