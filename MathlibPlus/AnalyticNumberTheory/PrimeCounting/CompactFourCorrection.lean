import MathlibPlus.CompactPrimeCounting

namespace MathlibPlus.AnalyticNumberTheory.PrimeCounting

noncomputable section

/-- Claim 827's four-correction denominator, with `L = log x`. -/
def compactFourCorrectionDenominator (A x : ℝ) : ℝ :=
  let L := Real.log x
  L - 1 - L⁻¹ - 3 * (L⁻¹) ^ 2 - A * (L⁻¹) ^ 3

/-- Claim 827's associated upper-bound expression `x / D_A(x)`. -/
def compactFourCorrectionUpperBound (A x : ℝ) : ℝ :=
  x / compactFourCorrectionDenominator A x

/-- On the source's positive-logarithm domain, the displayed denominator has
exactly the normalized polynomial `s_A(1 / log x)` from claim 827. -/
theorem compactFourCorrectionDenominator_normalization (A x : ℝ) (hx : 1 < x) :
    compactFourCorrectionDenominator A x =
      Real.log x * MathlibPlus.CompactPrimeCounting.compactPolynomial A (Real.log x)⁻¹ := by
  dsimp [compactFourCorrectionDenominator, MathlibPlus.CompactPrimeCounting.compactPolynomial]
  have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  field_simp

end

end MathlibPlus.AnalyticNumberTheory.PrimeCounting
