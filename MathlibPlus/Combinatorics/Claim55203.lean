import Mathlib

namespace MathlibPlus.Combinatorics.Claim55203

/-!
Formalization of the algebraic core of admitted claim 55203 (R-5425 S7).
The carrier `X` abstracts the proper algebraic subshift mentioned by the
source; no algebraic structure is used by this implication.
-/

/-- A left inverse makes `τ` injective, while failure of the corresponding
right-inverse identity makes it non-surjective. -/
theorem injective_not_surjective
    {X : Type*} {σ τ : X → X}
    (hστ : σ ∘ τ = id)
    (hτσ : τ ∘ σ ≠ id) :
    Function.Injective τ ∧ ¬ Function.Surjective τ := by
  constructor
  · intro x y hxy
    calc
      x = σ (τ x) := by
        simpa [Function.comp] using (congrFun hστ x).symm
      _ = σ (τ y) := by rw [hxy]
      _ = y := by
        simpa [Function.comp] using congrFun hστ y
  · intro hsurj
    apply hτσ
    funext x
    obtain ⟨y, hy⟩ := hsurj x
    calc
      τ (σ x) = τ (σ (τ y)) := by rw [hy]
      _ = τ y := by
        rw [show σ (τ y) = y by
          simpa [Function.comp] using congrFun hστ y]
      _ = x := hy

end MathlibPlus.Combinatorics.Claim55203
