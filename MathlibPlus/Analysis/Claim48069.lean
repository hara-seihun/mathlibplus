import Mathlib.Analysis.Complex.Trigonometric

namespace MathlibPlus.Analysis.Claim48069

/-- The explicit reflected-atom expansion in the first substatement of claim 48069. -/
theorem reflectedAtomExpansion_claim48069
    (lam r : ℝ) (_hlam : 0 < lam) (_hr : 0 < r) (z : ℂ) :
    ((1 : ℂ) + (r : ℂ) * Complex.exp ((lam : ℂ) * z)) *
        ((1 : ℂ) + (r : ℂ) * Complex.exp (-((lam : ℂ) * z))) =
      1 + 2 * (r : ℂ) * Complex.cosh ((lam : ℂ) * z) + (r : ℂ) ^ 2 := by
  simp only [Complex.cosh, Complex.exp_neg]
  have he : Complex.exp ((lam : ℂ) * z) ≠ 0 := Complex.exp_ne_zero _
  field_simp [he]
  ring

end MathlibPlus.Analysis.Claim48069
