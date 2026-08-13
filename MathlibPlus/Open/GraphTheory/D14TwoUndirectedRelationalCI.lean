import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The dihedral group of order fourteen has simultaneous CI for two labelled
simple undirected Cayley relations. -/
def dihedralFourteenTwoUndirectedRelationalCI : Prop :=
  let N := Multiplicative (ZMod 7)
  let C := Multiplicative (ZMod 2)
  let IsInversionAction := fun φ : C →* MulAut N =>
    ∀ c n, φ c n = if c = 1 then n else n⁻¹
  (∃ φ, IsInversionAction φ) ∧
  ∀ (φ : C →* MulAut N), IsInversionAction φ →
    let G := N ⋊[φ] C
    ∀ (S T : Fin 2 → Set G) (e : G ≃ G),
      (∀ i, 1 ∉ S i) →
      (∀ i, 1 ∉ T i) →
      (∀ i x, x⁻¹ ∈ S i ↔ x ∈ S i) →
      (∀ i x, x⁻¹ ∈ T i ↔ x ∈ T i) →
      (∀ i x y, x⁻¹ * y ∈ S i ↔ (e x)⁻¹ * e y ∈ T i) →
      ∃ α : G ≃* G, ∀ i, α '' S i = T i

end MathlibPlus.Open.GraphTheory
