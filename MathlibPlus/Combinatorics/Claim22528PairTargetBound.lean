import Mathlib

namespace MathlibPlus.Combinatorics.Claim22528

/-- A selected pair-union target has one pair-coordinate in each of the three
role-class products. If each coordinate map is injective, the number of
selected targets is bounded by each product, hence by their minimum. -/
theorem pair_target_bound_claim22528
    {A₀ A₁ A₂ T : Type*}
    [Fintype A₀] [Fintype A₁] [Fintype A₂] [Fintype T]
    (f₀₁ : T → A₀ × A₁) (f₀₂ : T → A₀ × A₂) (f₁₂ : T → A₁ × A₂)
    (h₀₁ : Function.Injective f₀₁)
    (h₀₂ : Function.Injective f₀₂)
    (h₁₂ : Function.Injective f₁₂) :
    Fintype.card T ≤
      min (Fintype.card A₀ * Fintype.card A₁)
        (min (Fintype.card A₀ * Fintype.card A₂)
          (Fintype.card A₁ * Fintype.card A₂)) := by
  have h₀₁' : Fintype.card T ≤ Fintype.card (A₀ × A₁) :=
    Fintype.card_le_of_injective f₀₁ h₀₁
  have h₀₂' : Fintype.card T ≤ Fintype.card (A₀ × A₂) :=
    Fintype.card_le_of_injective f₀₂ h₀₂
  have h₁₂' : Fintype.card T ≤ Fintype.card (A₁ × A₂) :=
    Fintype.card_le_of_injective f₁₂ h₁₂
  have h₀₁'' : Fintype.card T ≤ Fintype.card A₀ * Fintype.card A₁ := by
    simpa using h₀₁'
  have h₀₂'' : Fintype.card T ≤ Fintype.card A₀ * Fintype.card A₂ := by
    simpa using h₀₂'
  have h₁₂'' : Fintype.card T ≤ Fintype.card A₁ * Fintype.card A₂ := by
    simpa using h₁₂'
  exact le_min h₀₁'' (le_min h₀₂'' h₁₂'')

end MathlibPlus.Combinatorics.Claim22528
