import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The scalar fixed-point-free semidirect product `C₇² ⋊ C₃` has no
ordinary undirected Cayley CI defect through valency ten. -/
def c7SquareScalarOrderThreeValencyAtMostTenCI : Prop :=
  let V := Multiplicative (Fin 2 → ZMod 7)
  let C := Multiplicative (ZMod 3)
  (∃ φ : C →* MulAut V,
      ∀ v : V,
        φ (.ofAdd 1) v =
          .ofAdd (fun i => 2 * (Multiplicative.toAdd v) i)) ∧
  ∀ (φ : C →* MulAut V),
    (∀ v : V,
      φ (.ofAdd 1) v =
        .ofAdd (fun i => 2 * (Multiplicative.toAdd v) i)) →
    let G := V ⋊[φ] C
    Nat.card G = 147 ∧
    ∀ (S T : Set G),
      1 ∉ S →
      1 ∉ T →
      (∀ x, x ∈ S ↔ x⁻¹ ∈ S) →
      (∀ x, x ∈ T ↔ x⁻¹ ∈ T) →
      S.ncard ≤ 10 →
      (∃ q : G ≃ G, ∀ x y : G,
        x⁻¹ * y ∈ S ↔ (q x)⁻¹ * q y ∈ T) →
      ∃ α : G ≃* G, α '' S = T

end MathlibPlus.Open.GraphTheory
