import Mathlib

namespace MathlibPlus.Analysis.Claim15033

/-- The literal center and endpoint coefficients in claim 15033.  The hypotheses
expose the carrier evaluation and the coefficient definition rather than
silently identifying them with unrelated functions. -/
theorem literal_center_coefficient
    (lambda b chi q A : ℝ)
    (hchi : chi = 1)
    (hq : q = lambda⁻¹ ^ 2 * chi - b)
    (hA : A = -q / (2 * Real.sqrt lambda)) :
    q = lambda⁻¹ ^ 2 - b ∧
      A = -(lambda⁻¹ ^ 2 - b) / (2 * Real.sqrt lambda) := by
  constructor
  · rw [hq, hchi]
    simp
  · rw [hA, hq, hchi]
    simp

end MathlibPlus.Analysis.Claim15033
