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

end MathlibPlus.Algebra.ChernArithmetic
