import Mathlib

namespace MathlibPlus.Open.R1818

private abbrev C5 := Multiplicative (ZMod 5)
private abbrev C7 := Multiplicative (ZMod 7)
private abbrev C3 := Multiplicative (ZMod 3)
private abbrev E73 (φ : C3 →* MulAut C7) := C7 ⋊[φ] C3

private def faithfulNontrivial (φ : C3 →* MulAut C7) : Prop :=
  φ (.ofAdd 1) ≠ 1

private def ordinaryUndirectedCI (G : Type*) [Group G] : Prop :=
  ∀ S T : Set G,
    1 ∉ S → 1 ∉ T →
    (∀ s : G, s ∈ S ↔ s⁻¹ ∈ S) →
    (∀ t : G, t ∈ T ↔ t⁻¹ ∈ T) →
    (∃ e : G ≃ G, ∀ x y : G,
      x⁻¹ * y ∈ S ↔ (e x)⁻¹ * e y ∈ T) →
    ∃ α : G ≃* G, α '' S = T

/-- Claim 32582: the exact order-105 Frobenius product is an ordinary
undirected CI-group for its faithful nontrivial order-three action. -/
def claim32582 : Prop :=
  ∀ (φ : C3 →* MulAut C7),
    faithfulNontrivial φ →
    let G := C5 × E73 φ
    Nat.card G = 105 ∧ ordinaryUndirectedCI G

end MathlibPlus.Open.R1818
