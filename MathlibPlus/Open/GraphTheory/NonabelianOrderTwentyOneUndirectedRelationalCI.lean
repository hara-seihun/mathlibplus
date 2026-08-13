import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The nonabelian group of order twenty-one has simultaneous CI for every
family of simple undirected right-Cayley relations. -/
def nonabelianOrderTwentyOneUndirectedRelationalCI : Prop :=
  ∀ (G : Type*) [Fintype G] [Group G] (a b : G),
    Fintype.card G = 21 →
    orderOf a = 7 →
    orderOf b = 3 →
    b * a * b⁻¹ = a ^ 2 →
    Subgroup.closure ({a, b} : Set G) = ⊤ →
    ∀ (ι : Type) (S T : ι → Set G) (e : G ≃ G),
      (∀ i, (1 : G) ∉ S i) →
      (∀ i, (1 : G) ∉ T i) →
      (∀ i, S i = (S i)⁻¹) →
      (∀ i, T i = (T i)⁻¹) →
      (∀ i x y, x⁻¹ * y ∈ S i ↔ (e x)⁻¹ * e y ∈ T i) →
        ∃ φ : G ≃* G, ∀ i, φ '' S i = T i

end MathlibPlus.Open.GraphTheory
