import Mathlib

namespace MathlibPlus.Analysis

/-- The width choice in claim 9496 is always available for a selected point
whose real part is greater than one half.  The source does not provide a
formal predicate for being a Xi zero, so the zero is retained only through
its displayed decomposition. -/
theorem gaussianParameterExists_claim9496
    (ρ : ℂ) (β γ : ℝ)
    (hρ : ρ = (β : ℂ) + (γ : ℂ) * Complex.I)
    (hβ : (1 : ℝ) / 2 < β) :
    ∃ α : ℝ, 0 < α ∧ α ^ 2 = 1 / β := by
  have hβ0 : 0 < β := by linarith
  have hratio : 0 < (1 : ℝ) / β := by positivity
  refine ⟨Real.sqrt (1 / β), Real.sqrt_pos.2 hratio, ?_⟩
  exact Real.sq_sqrt (le_of_lt hratio)

