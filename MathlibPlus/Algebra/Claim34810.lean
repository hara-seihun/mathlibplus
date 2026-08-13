import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim34810

/-- The rational comparison used by the square-grid nonoptimality corollary. -/
theorem squareGridRationalBound {m : ℕ} (hm : 10 ≤ m) :
    ((m : ℚ) + 1) ^ 2 + 6 * ((m : ℚ) - 1) <
      (4995 / 2756 : ℚ) * (m : ℚ) ^ 2 := by
  have hm' : (10 : ℚ) ≤ (m : ℚ) := by
    exact_mod_cast hm
  nlinarith [sq_nonneg ((m : ℚ) - 10)]

end MathlibPlus.Algebra.Claim34810
