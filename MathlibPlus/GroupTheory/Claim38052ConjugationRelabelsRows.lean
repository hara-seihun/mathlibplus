import Mathlib

namespace MathlibPlus.GroupTheory.Claim38052

/-- Claim 38052: conjugation by `alpha × 1` preserves the base permutation and
relabels each fiber row by the alpha-indexed permutation. -/
def conjugationRelabelsFiberRows : Prop :=
  ∀ (A B : Type*)
    (α σ : Equiv.Perm A)
    (q : A → Equiv.Perm B),
    α * σ = σ * α →
      let f : A × B → A × B := fun p =>
        (σ p.1, q p.1 p.2)
      let Φ : A × B ≃ A × B :=
        Equiv.prodCongr α (Equiv.refl B)
      ∀ a : A, ∀ b : B,
        Φ.symm (f (Φ (a, b))) =
          (σ a, q (α a) b)

end MathlibPlus.GroupTheory.Claim38052
