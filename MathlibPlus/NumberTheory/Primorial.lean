import Mathlib

namespace MathlibPlus.NumberTheory

/-- The exceptional ninth primorial is exactly `223092870`. -/
theorem exceptionalNinthPrimorial :
    (2 : ℕ) * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 = 223092870 := by
  norm_num

end MathlibPlus.NumberTheory
