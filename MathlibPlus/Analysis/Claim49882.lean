import Mathlib

namespace MathlibPlus.Analysis.Claim49882

/-- The exact rational arithmetic residue of the finite policy lower bound in claim 49882.

This theorem records the displayed lower-bound expression only; the policy semantics
and the definition of `L_4096` remain outside this arithmetic carrier. -/
theorem lowerBoundArithmetic_claim49882 :
    (32 : ℚ) * (4064 : ℚ) ^ 2 / (4 * (4096 : ℚ) ^ 2) *
        (1 - (32 : ℚ) * 31 / 4096) = 1564513 / 262144 ∧
      (2 : ℚ) < 1564513 / 262144 := by
  norm_num

end MathlibPlus.Analysis.Claim49882
