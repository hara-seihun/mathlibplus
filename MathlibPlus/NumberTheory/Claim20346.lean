import Mathlib

namespace MathlibPlus.NumberTheory.Claim20346

/-- The exact integer comparison recorded as the final comparison in
claim 20346's prime-17 estimate.  The preceding Salem-number transfer is a
separate analytic source interface. -/
theorem integerComparison :
    6 * 101 ^ 102 < 17 * 100 ^ 102 := by
  norm_num

end MathlibPlus.NumberTheory.Claim20346
