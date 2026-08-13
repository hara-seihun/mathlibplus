import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The first two previously open valency rows and their complements on
`Q₂₂₀ = QuaternionGroup 55` have the ordinary undirected Cayley CI property. -/
def dicyclicTwoTwentyValencyTenElevenComplementaryCI : Prop :=
  let G := QuaternionGroup 55
  Nat.card G = 220 ∧
  ∀ (S T : Set G),
    S = S⁻¹ →
    T = T⁻¹ →
    1 ∉ S →
    1 ∉ T →
    S.ncard = T.ncard →
    S.ncard ∈ ({10, 11, 208, 209} : Set ℕ) →
    (∃ e : G ≃ G, ∀ x y, x⁻¹ * y ∈ S ↔ (e x)⁻¹ * e y ∈ T) →
    ∃ α : G ≃* G, α '' S = T

end MathlibPlus.Open.GraphTheory
