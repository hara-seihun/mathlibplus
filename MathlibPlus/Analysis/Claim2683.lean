import Mathlib

namespace MathlibPlus.Analysis.Claim2683

/-- The multiplier displayed in admitted claim 2683 is entire and has no zeros.
The source does not provide a Lean interface for the transform `S_{α,k}`, so the
multiplier itself is formalized exactly. -/
theorem criticalMellinMultiplier_entire_and_ne_zero (α : ℂ) (k : ℕ) :
    Differentiable ℂ (fun z : ℂ => Complex.exp (-α * z ^ (2 * k))) ∧
      ∀ z : ℂ, Complex.exp (-α * z ^ (2 * k)) ≠ 0 := by
  constructor
  · apply Complex.differentiable_exp.comp
    fun_prop
  · intro z
    exact Complex.exp_ne_zero _

end MathlibPlus.Analysis.Claim2683
