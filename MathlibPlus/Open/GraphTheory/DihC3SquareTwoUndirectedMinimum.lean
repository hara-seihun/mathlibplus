import Mathlib

open scoped Classical

namespace MathlibPlus.Open.GraphTheory

/-- The first two-symbol undirected relational defect on `Dih(C₃²)` has total
valency six and is unique at that minimum, up to source/target automorphisms,
reversal, and interchange of the two relation symbols. -/
def dihedralC3SquareTwoUndirectedRelationMinimumClassification : Prop :=
  let N := Multiplicative (ZMod 3 × ZMod 3)
  let C := Multiplicative (ZMod 2)
  let IsInversionAction := fun φ : C →* MulAut N =>
    ∀ c n, φ c n = if c = 1 then n else n⁻¹
  (∃ φ, IsInversionAction φ) ∧
  ∀ (φ : C →* MulAut N), IsInversionAction φ →
    let G := N ⋊[φ] C
    let g := fun (a b : ZMod 3) (e : ZMod 2) =>
      (⟨Multiplicative.ofAdd (a, b), Multiplicative.ofAdd e⟩ : G)
    let enum : Fin 18 → G := ![
      g 0 0 0, g 0 1 0, g 0 2 0, g 1 0 0, g 1 1 0, g 1 2 0,
      g 2 0 0, g 2 1 0, g 2 2 0, g 0 0 1, g 0 1 1, g 0 2 1,
      g 1 0 1, g 1 1 1, g 1 2 1, g 2 0 1, g 2 1 1, g 2 2 1]
    let qi : Fin 18 → Fin 18 := ![
      0, 5, 2, 7, 8, 1, 6, 3, 4, 9, 12, 14, 10, 17, 11, 16, 15, 13]
    ∃ (S₀ T₀ : Fin 2 → Set G) (q₀ : G ≃ G),
      (S₀ 0 = {g 0 0 1, g 0 1 1, g 1 0 1} ∧
        T₀ 0 = {g 0 0 1, g 0 1 1, g 1 0 1} ∧
        S₀ 1 = {g 0 2 1, g 2 0 1, g 2 2 1} ∧
        T₀ 1 = {g 1 1 1, g 1 2 1, g 2 1 1}) ∧
      (∀ i, q₀ (enum i) = enum (qi i)) ∧
      q₀ 1 = 1 ∧
      (∀ x : G, q₀ (q₀ x) = x) ∧
      (∀ i, 1 ∉ S₀ i ∧ 1 ∉ T₀ i) ∧
      (∀ i x, (x ∈ S₀ i ↔ x⁻¹ ∈ S₀ i) ∧
        (x ∈ T₀ i ↔ x⁻¹ ∈ T₀ i)) ∧
      (∀ i, T₀ i = q₀ '' S₀ i) ∧
      (∀ i x y, x⁻¹ * y ∈ S₀ i ↔ (q₀ x)⁻¹ * q₀ y ∈ T₀ i) ∧
      (∀ i, (S₀ i).ncard = 3 ∧ (T₀ i).ncard = 3) ∧
      Disjoint (S₀ 0) (S₀ 1) ∧ Disjoint (T₀ 0) (T₀ 1) ∧
      (∀ i, ∃ α : G ≃* G, α '' S₀ i = T₀ i) ∧
      (∀ i, Nat.card {α : G ≃* G // α '' S₀ i = T₀ i} = 6) ∧
      (¬ ∃ α : G ≃* G, ∀ i, α '' S₀ i = T₀ i) ∧
      (∀ (S T : Fin 2 → Set G) (q : G ≃ G),
        q 1 = 1 →
        (∀ i, 1 ∉ S i ∧ 1 ∉ T i) →
        (∀ i x, (x ∈ S i ↔ x⁻¹ ∈ S i) ∧
          (x ∈ T i ↔ x⁻¹ ∈ T i)) →
        (∀ i x y, x⁻¹ * y ∈ S i ↔ (q x)⁻¹ * q y ∈ T i) →
        (¬ ∃ α : G ≃* G, ∀ i, α '' S i = T i) →
        6 ≤ (S 0).ncard + (S 1).ncard) ∧
      ∀ (S T : Fin 2 → Set G) (q : G ≃ G),
        q 1 = 1 →
        (∀ i, 1 ∉ S i ∧ 1 ∉ T i) →
        (∀ i x, (x ∈ S i ↔ x⁻¹ ∈ S i) ∧
          (x ∈ T i ↔ x⁻¹ ∈ T i)) →
        (∀ i x y, x⁻¹ * y ∈ S i ↔ (q x)⁻¹ * q y ∈ T i) →
        (¬ ∃ α : G ≃* G, ∀ i, α '' S i = T i) →
        (S 0).ncard + (S 1).ncard = 6 →
        ∃ σ : Fin 2 ≃ Fin 2,
          (∃ α β : G ≃* G,
            ∀ i, α '' S i = S₀ (σ i) ∧ β '' T i = T₀ (σ i)) ∨
          (∃ α β : G ≃* G,
            ∀ i, α '' S i = T₀ (σ i) ∧ β '' T i = S₀ (σ i))

end MathlibPlus.Open.GraphTheory
