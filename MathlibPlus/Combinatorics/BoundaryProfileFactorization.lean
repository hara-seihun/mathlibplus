import Mathlib

namespace MathlibPlus.Combinatorics

/-- The abstract factorization core of admitted claim 23165: for a surjective
profile, an evaluation factors uniquely through the profile exactly when it is
constant on profile fibers. -/
theorem factorThrough_iff_constantOnFibers
    {α β D : Type*} (q : α → β) (hq : Function.Surjective q)
    (Φ : α → D) :
    (∃! ψ : β → D, ∀ x, ψ (q x) = Φ x) ↔
      ∀ x y, q x = q y → Φ x = Φ y := by
  constructor
  · rintro ⟨ψ, hψ, -⟩ x y hxy
    rw [← hψ x, ← hψ y, hxy]
  · intro h
    let ψ : β → D := fun b => Φ (Classical.choose (hq b))
    have hψ : ∀ x, ψ (q x) = Φ x := by
      intro x
      dsimp [ψ]
      exact h _ _ (Classical.choose_spec (hq (q x)))
    refine ⟨ψ, hψ, ?_⟩
    intro ψ' hψ'
    funext b
    obtain ⟨x, rfl⟩ := hq b
    exact (hψ' x).trans (hψ x).symm

end MathlibPlus.Combinatorics
