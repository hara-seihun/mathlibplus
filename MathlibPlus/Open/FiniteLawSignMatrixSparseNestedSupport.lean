import Mathlib

namespace MathlibPlus.Open

/-- A finite-column sign law with a sparse, nested support realizes a prescribed
function whose values lie in the interval `[-1, 1]`. -/
def finiteLawSignMatrixSparseNestedSupport
    {α : Type*} (C : Finset α)
    (f : C → Set.Icc (-1 : ℝ) 1) : Prop :=
  ∃ Λ : (C → ({-1, 1} : Set ℝ)) →₀ ℝ,
    (∀ T, 0 ≤ Λ T) ∧
    ((∑ T ∈ Λ.support, Λ T) = 1) ∧
    (Λ.support.card ≤ C.card + 1) ∧
    (∀ O, (∑ T ∈ Λ.support, Λ T * (T O : ℝ)) = (f O : ℝ)) ∧
    (∀ T₁ ∈ Λ.support, ∀ T₂ ∈ Λ.support,
      {O : C | (T₁ O : ℝ) = 1} ⊆ {O : C | (T₂ O : ℝ) = 1} ∨
      {O : C | (T₂ O : ℝ) = 1} ⊆ {O : C | (T₁ O : ℝ) = 1})

end MathlibPlus.Open
