import MathlibPlus.Basic

namespace MathlibPlus.Algebra

/-- The inverse of a same-sign adjacent equation satisfies the corresponding
inverse same-sign adjacent equation. -/
theorem claim41330_inverseAdjacentEquation
    {G H : Type*} [AddGroup G] [AddGroup H]
    (σ : G ≃ H) (τ : G ≃ H)
    (h : ∀ B z : G, σ (B + 2 • z) = σ B + 2 • τ z) :
    ∀ C w : H, σ.symm (C + 2 • w) =
      σ.symm C + 2 • τ.symm w := by
  intro C w
  have hmain := h (σ.symm C) (τ.symm w)
  simpa using (congrArg σ.symm hmain).symm

end MathlibPlus.Algebra
