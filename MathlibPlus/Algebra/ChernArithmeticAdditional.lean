import Mathlib

namespace MathlibPlus.Algebra.ChernArithmeticAdditional

/-!
Numerical formalizations of admitted claims 14605, 14608, 14619, and 14621.
The source claims are arithmetic filters for specified Chern-number pairs; they
carry no surface object or existence hypothesis, so the declarations below
formalize exactly those displayed rational/integer calculations.
-/

/-- Claim 14605: the pair `(c₁², c₂) = (4, 8)` passes positivity. -/
theorem c1sq4_c2_8_positive : (0 : ℚ) < 4 ∧ (0 : ℚ) < 8 := by
  norm_num

/-- Claim 14608: for `(c₁², c₂) = (4, 8)`, the Chern sum is twelve and is
therefore divisible by twelve. -/
theorem c1sq4_c2_8_noether_divisibility :
    (12 : ℤ) ∣ (4 + 8) ∧ (4 + 8 : ℤ) = 12 := by
  norm_num

/-- Claim 14619: for `(c₁², c₂) = (6, 6)`, the displayed Noether inequality
is the exact numerical inequality `30 ≥ -30`. -/
theorem c1sq6_c2_6_noether_inequality :
    (5 : ℚ) * 6 = 30 ∧ (30 : ℚ) ≥ 6 - 36 := by
  norm_num

/-- Claim 14621: for `(c₁², c₂) = (6, 6)`, the Chern sum is twelve and is
therefore divisible by twelve. -/
theorem c1sq6_c2_6_noether_divisibility :
    (12 : ℤ) ∣ (6 + 6) ∧ (6 + 6 : ℤ) = 12 := by
  norm_num

end MathlibPlus.Algebra.ChernArithmeticAdditional
