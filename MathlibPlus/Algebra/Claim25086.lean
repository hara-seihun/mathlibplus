import Mathlib

namespace MathlibPlus.Algebra.Claim25086

/-- The displayed distance-two swap factorization, with the two matching
pairings represented by the four block products.  The partition hypotheses do
not add algebraic equations once these products are fixed. -/
theorem distanceTwoSwapFactorization_claim25086 {R : Type*} [CommRing R]
    (P_A P_B P_C P_D : R) :
    (P_A * P_C + P_B * P_D) - (P_A * P_D + P_B * P_C) =
      (P_A - P_B) * (P_C - P_D) := by
  ring

end MathlibPlus.Algebra.Claim25086
