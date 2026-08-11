import Mathlib

/-!
# Arithmetic checks for the Chern pair `(7, 5)`

Exact arithmetic formalizations of admitted claims 14623--14626.  The source
claims do not specify an ambient ordered field; `ℚ` is used here so that the
Noether quotient and the displayed inequalities are all expressed exactly.
These declarations formalize only the numerical checks, not existence of a
surface with this Chern pair.
-/

namespace MathlibPlus.Algebra.ChernArithmetic

/-- The displayed Noether quotient for `(c₁², c₂) = (7, 5)` is one. -/
theorem c1sq7_c2_5_euler : ((7 : ℚ) + 5) / 12 = 1 := by
  norm_num

/-- Both entries of the pair `(7, 5)` are positive. -/
theorem c1sq7_c2_5_positive : (0 : ℚ) < 7 ∧ (0 : ℚ) < 5 := by
  norm_num

/-- The displayed numerical Noether inequality for `(7, 5)`. -/
theorem c1sq7_c2_5_noether : (5 : ℚ) - 36 ≤ 5 * 7 := by
  norm_num

/-- The Bogomolov--Miyaoka--Yau numerical inequality for `(7, 5)`. -/
theorem c1sq7_c2_5_bmy : (7 : ℚ) ≤ 3 * 5 := by
  norm_num

/-- Claim 14600: the displayed BMY inequality for `(c₁², c₂) = (3, 9)`. -/
theorem c1sq3_c2_9_bmy : (3 : ℚ) ≤ 3 * 9 := by
  norm_num

/-- Claim 14607: the displayed BMY inequality for `(c₁², c₂) = (4, 8)`. -/
theorem c1sq4_c2_8_bmy : (4 : ℚ) ≤ 3 * 8 := by
  norm_num

/-- Claim 14614: the displayed BMY inequality for `(c₁², c₂) = (5, 7)`. -/
theorem c1sq5_c2_7_bmy : (5 : ℚ) ≤ 3 * 7 := by
  norm_num

/-- Claim 14633: the displayed BMY equality for `(c₁², c₂) = (9, 3)`. -/
theorem c1sq9_c2_3_bmy_eq : (9 : ℚ) = 3 * 3 := by
  norm_num

end MathlibPlus.Algebra.ChernArithmetic
