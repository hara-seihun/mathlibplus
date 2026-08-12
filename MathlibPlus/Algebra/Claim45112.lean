import Mathlib

namespace MathlibPlus.Algebra.Claim45112

/-- The exact numerical consequences in claim 45112. -/
theorem support_counts
    (a x y z : ℕ)
    (h₁ : a + 3 * x + 3 * y + z = 67)
    (h₂ : x + 2 * y + z = 28)
    (ha : a = 9) (hz : z = 1) :
    x = 11 ∧ y = 8 ∧
      9 + 3 * 11 + 3 * 8 + 1 = 67 ∧
      11 + 2 * 8 + 1 = 28 ∧
      9 + 2 * 11 + 8 = 39 := by
  omega

end MathlibPlus.Algebra.Claim45112
