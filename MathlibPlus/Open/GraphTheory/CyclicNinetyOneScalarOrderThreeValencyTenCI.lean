import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Both fixed-point-free scalar actions on the cyclic kernel of order 91 are
ordinary undirected CI through valency ten and in the complementary high band. -/
def cyclicNinetyOneScalarOrderThreeValencyTenCI : Prop :=
  ∀ l : ZMod 91, (l = 9 ∨ l = 16) →
    (∃ action : Multiplicative (ZMod 3) →* MulAut (Multiplicative (ZMod 91)),
      ∀ x : Multiplicative (ZMod 91),
        action (.ofAdd 1) x = .ofAdd (l * x.toAdd)) ∧
    ∀ action : Multiplicative (ZMod 3) →* MulAut (Multiplicative (ZMod 91)),
      (∀ x : Multiplicative (ZMod 91),
        action (.ofAdd 1) x = .ofAdd (l * x.toAdd)) →
      let G := Multiplicative (ZMod 91) ⋊[action] Multiplicative (ZMod 3)
      Nat.card G = 273 ∧
      ∀ S T : Set G,
        S = S⁻¹ → T = T⁻¹ → 1 ∉ S → 1 ∉ T →
        ((Set.ncard S ≤ 10 ∧ Set.ncard T ≤ 10) ∨
          (262 ≤ Set.ncard S ∧ 262 ≤ Set.ncard T)) →
        (∃ q : G ≃ G, ∀ x y,
          x⁻¹ * y ∈ S ↔ (q x)⁻¹ * q y ∈ T) →
        ∃ α : G ≃* G, α '' S = T

end MathlibPlus.Open.GraphTheory
