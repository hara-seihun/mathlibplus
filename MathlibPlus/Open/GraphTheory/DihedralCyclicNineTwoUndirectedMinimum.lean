import Mathlib

open scoped Classical

namespace MathlibPlus.Open.GraphTheory

/-- The first two-symbol undirected relational defect on `Dih(C₉)` has total
valency five and is unique at that minimum, up to source/target automorphisms,
reversal, and interchange of relation symbols. -/
def dihedralCyclicNineTwoUndirectedRelationMinimumClassification : Prop :=
  let N := Multiplicative (ZMod 9)
  let C := Multiplicative (ZMod 2)
  let IsInversionAction := fun φ : C →* MulAut N =>
    ∀ c n, φ c n = if c = 1 then n else n⁻¹
  (∃ φ, IsInversionAction φ) ∧
  ∀ (φ : C →* MulAut N), IsInversionAction φ →
    let G := N ⋊[φ] C
    ∃ (S₀ T₀ : Fin 2 → Set G) (q₀ : G ≃ G),
      q₀ 1 = 1 ∧
      (∀ x : G, q₀ (q₀ x) = x) ∧
      (∀ i, 1 ∉ S₀ i ∧ 1 ∉ T₀ i) ∧
      (∀ i x, (x ∈ S₀ i ↔ x⁻¹ ∈ S₀ i) ∧
        (x ∈ T₀ i ↔ x⁻¹ ∈ T₀ i)) ∧
      (∀ i, T₀ i = q₀ '' S₀ i) ∧
      (∀ i x y, x⁻¹ * y ∈ S₀ i ↔ (q₀ x)⁻¹ * q₀ y ∈ T₀ i) ∧
      (S₀ 0).ncard = 1 ∧ (T₀ 0).ncard = 1 ∧
      (S₀ 1).ncard = 4 ∧ (T₀ 1).ncard = 4 ∧
      Disjoint (S₀ 0) (S₀ 1) ∧ Disjoint (T₀ 0) (T₀ 1) ∧
      Nat.card {α : G ≃* G // α '' S₀ 0 = T₀ 0} = 6 ∧
      Nat.card {α : G ≃* G // α '' S₀ 1 = T₀ 1} = 3 ∧
      (¬ ∃ α : G ≃* G, ∀ i, α '' S₀ i = T₀ i) ∧
      (∀ (S T : Fin 2 → Set G) (q : G ≃ G),
        q 1 = 1 →
        (∀ i, 1 ∉ S i ∧ 1 ∉ T i) →
        (∀ i x, (x ∈ S i ↔ x⁻¹ ∈ S i) ∧
          (x ∈ T i ↔ x⁻¹ ∈ T i)) →
        (∀ i x y, x⁻¹ * y ∈ S i ↔ (q x)⁻¹ * q y ∈ T i) →
        (¬ ∃ α : G ≃* G, ∀ i, α '' S i = T i) →
        5 ≤ (S 0).ncard + (S 1).ncard) ∧
      ∀ (S T : Fin 2 → Set G) (q : G ≃ G),
        q 1 = 1 →
        (∀ i, 1 ∉ S i ∧ 1 ∉ T i) →
        (∀ i x, (x ∈ S i ↔ x⁻¹ ∈ S i) ∧
          (x ∈ T i ↔ x⁻¹ ∈ T i)) →
        (∀ i x y, x⁻¹ * y ∈ S i ↔ (q x)⁻¹ * q y ∈ T i) →
        (¬ ∃ α : G ≃* G, ∀ i, α '' S i = T i) →
        (S 0).ncard + (S 1).ncard = 5 →
        ∃ σ : Fin 2 ≃ Fin 2,
          (∃ α β : G ≃* G,
            ∀ i, α '' S i = S₀ (σ i) ∧ β '' T i = T₀ (σ i)) ∨
          (∃ α β : G ≃* G,
            ∀ i, α '' S i = T₀ (σ i) ∧ β '' T i = S₀ (σ i))

end MathlibPlus.Open.GraphTheory
