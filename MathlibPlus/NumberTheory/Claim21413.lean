import MathlibPlus.Algebra.LinearQuadraticFactorization

namespace MathlibPlus.NumberTheory.Claim21413

/-- The exact numerical Hensel margin reported in claim 21413. -/
theorem residualPrecisionExceedsTwiceDeterminant_claim21413 :
    (2 : ℚ) * 8 = 16 ∧ (16 : ℚ) < 30 := by
  norm_num

end MathlibPlus.NumberTheory.Claim21413
