import Mathlib

namespace MathlibPlus.Open

/-- The presentation displayed in the admitted claim, with generators `a = 0`
and `b = 1`. -/
def coprimeShellProductsQ12CI : Prop :=
  let rels : Set (FreeGroup (Fin 2)) :=
    { (FreeGroup.of (0 : Fin 2)) ^ 6,
      (FreeGroup.of (1 : Fin 2)) ^ 2 *
        ((FreeGroup.of (0 : Fin 2)) ^ 3)⁻¹,
      (FreeGroup.of (1 : Fin 2))⁻¹ *
        FreeGroup.of (0 : Fin 2) *
        FreeGroup.of (1 : Fin 2) *
        FreeGroup.of (0 : Fin 2) }
  let Q12 := PresentedGroup rels
  let G := Multiplicative (ZMod 7) × Q12
  ∀ S T : Set G,
    (∀ s ∈ S, s ≠ 1) →
    (∀ s ∈ S, s⁻¹ ∈ S) →
    (S.ncard = T.ncard ∧ (S.ncard = 15 ∨ S.ncard = 68)) →
    (∀ t ∈ T, t ≠ 1) →
    (∀ t ∈ T, t⁻¹ ∈ T) →
    ∀ e : G ≃ G,
      (∀ x y,
        (∃ s ∈ S, y = x * s) ↔
          (∃ t ∈ T, e y = e x * t)) →
      ∃ α : G ≃* G,
        α '' S = T

end MathlibPlus.Open
