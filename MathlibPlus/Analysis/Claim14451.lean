import Mathlib

namespace MathlibPlus.Analysis.Claim14451

/-- Dividing a determinant by the positive ordered-knot Vandermonde factor
preserves its sign.  This is the exact collision-regularization implication
used in the source chamber. -/
theorem collisionRegularizedDeterminant
    {q₁ q₂ q₃ D R : ℝ}
    (h₁₂ : q₁ < q₂) (h₁₃ : q₁ < q₃) (h₂₃ : q₂ < q₃)
    (hR : R = D / ((q₂ - q₁) * (q₃ - q₁) * (q₃ - q₂))) :
    D > 0 ↔ R > 0 := by
  have hden : 0 < (q₂ - q₁) * (q₃ - q₁) * (q₃ - q₂) := by
    positivity
  rw [hR]
  change 0 < D ↔ 0 < D / ((q₂ - q₁) * (q₃ - q₁) * (q₃ - q₂))
  constructor
  · intro hD
    exact div_pos hD hden
  · intro hRpos
    rcases (div_pos_iff.mp hRpos) with h | h
    · exact h.1
    · exfalso
      linarith

end MathlibPlus.Analysis.Claim14451
