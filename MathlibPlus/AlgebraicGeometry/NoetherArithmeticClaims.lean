import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace MathlibPlus.AlgebraicGeometry

/-- Claim 14615: the Chern-number sum for `(c₁², c₂) = (5, 7)` is divisible
by twelve. -/
theorem noether_formula_divisibility_claim14615 :
    (12 : ℤ) ∣ (5 + 7 : ℤ) := by
  norm_num

/-- Claim 14651: each of the three displayed Chern-number pairs has sum `24`,
and hence its sum is divisible by twelve. -/
theorem noether_formula_divisibility_claim14651 :
    (12 : ℤ) ∣ (5 + 19 : ℤ) ∧
      (12 : ℤ) ∣ (6 + 18 : ℤ) ∧
      (12 : ℤ) ∣ (7 + 17 : ℤ) := by
  norm_num

end MathlibPlus.AlgebraicGeometry
