import Mathlib

namespace MathlibPlus.AlgebraicGeometry.Claim57351

/-- The numerical correction in claim 57351: both ordered pairs have Euler
characteristic two, but their defect values are different.  This records only
the displayed arithmetic; the source geography theorem is a separate carrier. -/
theorem correctedChernPairArithmetic_claim57351 :
    ((7 : ℤ) + 17) / 12 = 2 ∧
    ((17 : ℤ) + 7) / 12 = 2 ∧
    (9 : ℤ) * 2 - 17 = 1 ∧
    (9 : ℤ) * 2 - 7 = 11 ∧
    ((7 : ℤ), 17) ≠ ((17 : ℤ), 7) := by
  norm_num

end MathlibPlus.AlgebraicGeometry.Claim57351
