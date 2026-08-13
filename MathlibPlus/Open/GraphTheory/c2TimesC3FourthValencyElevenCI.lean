import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Ordinary undirected CI at valency 11 and its complementary valency 150
on `C₂ × C₃⁴`, certified by the complete native atom-layer census. -/
def c2TimesC3FourthValencyElevenCI : Prop :=
  let G := ZMod 2 × (Fin 4 → ZMod 3)
  ∀ (S T : Set G),
    (0 : G) ∉ S →
    (0 : G) ∉ T →
    (∀ x, x ∈ S ↔ -x ∈ S) →
    (∀ x, x ∈ T ↔ -x ∈ T) →
    (S.ncard = 11 ∨ S.ncard = 150) →
    (T.ncard = 11 ∨ T.ncard = 150) →
    ∀ e : G ≃ G,
      (∀ x y : G, y - x ∈ S ↔ e y - e x ∈ T) →
        ∃ α : G ≃+ G, α '' S = T

end MathlibPlus.Open.GraphTheory
