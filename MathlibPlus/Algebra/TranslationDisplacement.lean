import Mathlib

namespace MathlibPlus.Algebra.TranslationDisplacement

/-- Claim 28930: the displacement set of a translation is the singleton zero set. -/
theorem translation_displacement_subgroup {α : Type*} [AddCommGroup α] (t : α) :
    let p : α → α := fun x => x + t
    (∀ x : α, x - p x + p 0 = 0) ∧
      {y : α | ∃ x : α, y = x - p x + p 0} = ({0} : Set α) := by
  dsimp
  constructor
  · intro x
    simp [sub_eq_add_neg, add_comm]
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      simp [sub_eq_add_neg, add_comm]
    · intro hy
      have hy0 : y = 0 := by simpa using hy
      subst y
      refine ⟨0, ?_⟩
      simp [sub_eq_add_neg, add_comm]

end MathlibPlus.Algebra.TranslationDisplacement
