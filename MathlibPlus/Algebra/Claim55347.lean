import MathlibPlus.Basic

namespace MathlibPlus.Algebra

/-- The translation-normalization core of admitted claim 55347. -/
theorem translationNormalization_claim55347
    {A : Type*} [AddCommGroup A] [Fintype A] (f : A → A) :
    let g : A → A := fun x => f x - f 0
    g 0 = 0 ∧
      (∀ x y : A, g x - g y = f x - f y) ∧
      (∀ (Q : A → Prop) (x y : A),
        Q (f x - f y) ↔ Q (g x - g y)) := by
  dsimp
  constructor
  · simp
  constructor
  · intro x y
    abel
  · intro Q x y
    abel

end MathlibPlus.Algebra
