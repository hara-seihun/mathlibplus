import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace MathlibPlus.Open.GraphTheory

/-- The first two-symbol undirected relational defect on `D₁₈ = Dih(C₉)`
has total valency five and is unique at that minimum, up to independent
source/target automorphisms, source-target reversal, and label interchange. -/
def dihedralEighteenTwoUndirectedRelationMinimumClassification : Prop :=
  let G := DihedralGroup 9
  ∃ (S₀ T₀ : Fin 2 → Set G) (q₀ : G ≃ G),
    S₀ 0 = {DihedralGroup.sr 0} ∧
    T₀ 0 = {DihedralGroup.sr 0} ∧
    S₀ 1 = {DihedralGroup.sr 1, DihedralGroup.sr 3,
      DihedralGroup.sr 4, DihedralGroup.sr 7} ∧
    T₀ 1 = {DihedralGroup.sr 1, DihedralGroup.sr 4,
      DihedralGroup.sr 6, DihedralGroup.sr 7} ∧
    q₀ (DihedralGroup.r 0) = DihedralGroup.r 0 ∧
    q₀ (DihedralGroup.r 1) = DihedralGroup.r 1 ∧
    q₀ (DihedralGroup.r 2) = DihedralGroup.r 2 ∧
    q₀ (DihedralGroup.r 3) = DihedralGroup.r 6 ∧
    q₀ (DihedralGroup.r 4) = DihedralGroup.r 7 ∧
    q₀ (DihedralGroup.r 5) = DihedralGroup.r 8 ∧
    q₀ (DihedralGroup.r 6) = DihedralGroup.r 3 ∧
    q₀ (DihedralGroup.r 7) = DihedralGroup.r 4 ∧
    q₀ (DihedralGroup.r 8) = DihedralGroup.r 5 ∧
    q₀ (DihedralGroup.sr 0) = DihedralGroup.sr 0 ∧
    q₀ (DihedralGroup.sr 1) = DihedralGroup.sr 1 ∧
    q₀ (DihedralGroup.sr 2) = DihedralGroup.sr 2 ∧
    q₀ (DihedralGroup.sr 3) = DihedralGroup.sr 6 ∧
    q₀ (DihedralGroup.sr 4) = DihedralGroup.sr 7 ∧
    q₀ (DihedralGroup.sr 5) = DihedralGroup.sr 8 ∧
    q₀ (DihedralGroup.sr 6) = DihedralGroup.sr 3 ∧
    q₀ (DihedralGroup.sr 7) = DihedralGroup.sr 4 ∧
    q₀ (DihedralGroup.sr 8) = DihedralGroup.sr 5 ∧
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
    (∀ i, ∃ α : G ≃* G, α '' S₀ i = T₀ i) ∧
    Set.ncard {α : G ≃* G | α '' S₀ 0 = T₀ 0} = 6 ∧
    Set.ncard {α : G ≃* G | α '' S₀ 1 = T₀ 1} = 3 ∧
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
