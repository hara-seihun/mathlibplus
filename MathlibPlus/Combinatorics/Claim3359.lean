import Mathlib

namespace MathlibPlus.Combinatorics.Claim3359

/-- The exact capacity arithmetic in claim 3359: once the displayed value
`R(1,5)=1` is fixed, the outside capacity is zero rather than one. -/
theorem zeroCapacityWhenR15One_claim3359
    (R : ℕ → ℕ → ℕ) (hR : R 1 5 = 1) :
    R 1 5 - 1 = 0 ∧ R 1 5 - 1 ≠ 1 := by
  omega

end MathlibPlus.Combinatorics.Claim3359
