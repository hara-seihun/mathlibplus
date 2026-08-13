import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The nonabelian scalar Frobenius group `C₁₃ ⋊ C₃` is an ordinary
undirected CI-group. -/
def nonabelianOrderThirtyNineUndirectedCI : Prop :=
  let V := Multiplicative (ZMod 13)
  let C := Multiplicative (ZMod 3)
  (∃ φ : C →* MulAut V,
      ∀ v : V,
        φ (.ofAdd 1) v =
          .ofAdd (3 * Multiplicative.toAdd v)) ∧
  ∀ (φ : C →* MulAut V),
    (∀ v : V,
      φ (.ofAdd 1) v =
        .ofAdd (3 * Multiplicative.toAdd v)) →
    let G := V ⋊[φ] C
    Nat.card G = 39 ∧
    ∀ (S T : Set G),
      1 ∉ S →
      1 ∉ T →
      (∀ x, x ∈ S ↔ x⁻¹ ∈ S) →
      (∀ x, x ∈ T ↔ x⁻¹ ∈ T) →
      (∃ q : G ≃ G, ∀ x y : G,
        x⁻¹ * y ∈ S ↔ (q x)⁻¹ * q y ∈ T) →
      ∃ α : G ≃* G, α '' S = T

end MathlibPlus.Open.GraphTheory
