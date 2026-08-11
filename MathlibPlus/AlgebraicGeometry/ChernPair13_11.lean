import Mathlib

namespace MathlibPlus.AlgebraicGeometry

/-- The Chern-number pair `(c₁², c₂) = (13, 11)` passes exactly the four
numerical geography checks recorded in admitted claim 14676. -/
theorem chernPair13_11_numericallyAdmissible :
    (0 : ℤ) < 13 ∧
    (0 : ℤ) < 11 ∧
    (11 : ℤ) - 36 ≤ 5 * 13 ∧
    (13 : ℤ) ≤ 3 * 11 := by
  norm_num

end MathlibPlus.AlgebraicGeometry
