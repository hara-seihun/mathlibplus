import Mathlib

namespace MathlibPlus.AnalyticNumberTheory.Claim14707

/- The strict gap inequalities follow from the three displayed open interval
   enclosures; all decimal endpoints are exact rational real literals. -/
theorem certifiedZetaGapReversal
    (γ₂ γ₃ γ₄ : ℝ)
    (h₂ : 21.0220 < γ₂ ∧ γ₂ < 21.0221)
    (h₃ : 25.0108 < γ₃ ∧ γ₃ < 25.0109)
    (h₄ : 30.4248 < γ₄ ∧ γ₄ < 30.4249) :
    let g₂ : ℝ := γ₃ - γ₂
    let g₃ : ℝ := γ₄ - γ₃
    g₂ < 3.9889 ∧ g₃ > 5.4139 ∧ g₃ - g₂ > 1.4250 := by
  dsimp
  rcases h₂ with ⟨h₂lo, h₂hi⟩
  rcases h₃ with ⟨h₃lo, h₃hi⟩
  rcases h₄ with ⟨h₄lo, h₄hi⟩
  constructor
  · linarith
  constructor
  · linarith
  · linarith

