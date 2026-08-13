import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The cell-N3 group `E(C₁₅,8)` is ordinary undirected Cayley-CI at each
of valencies twelve and thirteen. -/
def eCyclicFifteenEightValencyTwelveAndThirteenCI : Prop :=
  let A := Multiplicative (ZMod 15)
  let C := Multiplicative (ZMod 8)
  let IsInversionAction := fun φ : C →* MulAut A =>
    ∀ a : A, φ (.ofAdd 1) a = a⁻¹
  (∃ φ, IsInversionAction φ) ∧
  ∀ (φ : C →* MulAut A), IsInversionAction φ →
    let G := A ⋊[φ] C
    Nat.card G = 120 ∧
    ∀ S T : Set G,
      1 ∉ S →
      1 ∉ T →
      (∀ x, x ∈ S ↔ x⁻¹ ∈ S) →
      (∀ x, x ∈ T ↔ x⁻¹ ∈ T) →
      ((S.ncard = 12 ∧ T.ncard = 12) ∨
        (S.ncard = 13 ∧ T.ncard = 13)) →
      (∃ q : G ≃ G, ∀ x y : G,
        x⁻¹ * y ∈ S ↔ (q x)⁻¹ * q y ∈ T) →
      ∃ α : G ≃* G, α '' S = T

end MathlibPlus.Open.GraphTheory
