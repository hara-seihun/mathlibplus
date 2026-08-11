import Mathlib

namespace MathlibPlus.Analysis

/-- Claim 15375: a differentiable even real function has zero derivative at the
origin.  The source's `f'(0)` is represented by `deriv f 0`. -/
theorem differentiableEvenDerivZero_claim15375 (f : ℝ → ℝ)
    (h_diff : Differentiable ℝ f) (h_even : Function.Even f) :
    deriv f 0 = 0 := by
  have hf : HasDerivAt f (deriv f 0) 0 :=
    (h_diff 0).hasDerivAt
  have hfneg : HasDerivAt f (deriv f 0) (-0 : ℝ) := by
    simpa using hf
  have hneg : HasDerivAt (f ∘ Neg.neg) (deriv f 0 * (-1 : ℝ)) 0 := by
    simpa using hfneg.comp 0 (hasDerivAt_neg (0 : ℝ))
  have hsame : f ∘ Neg.neg = f := by
    funext x
    exact h_even x
  rw [hsame] at hneg
  have heq : deriv f 0 = deriv f 0 * (-1 : ℝ) := hf.unique hneg
  linarith

end MathlibPlus.Analysis
