import Mathlib

namespace MathlibPlus.Arithmetic

/--
Formalization of admitted claim 20171.  The parameter `t` is kept arbitrary: its
ambient domain was not specified in the claim, and the asserted length is
independent of it once the displayed definition of `U` is used.
-/
theorem firstDyadicBlockLength (t : ℝ) :
    let U : ℝ → ℝ := fun N => N ^ 2 - t / 16
    U 690989 ≤ U 1381978 ∧
      U 1381978 - U 690989 =
        (2 * (690989 : ℝ)) ^ 2 - (690989 : ℝ) ^ 2 ∧
      (2 * (690989 : ℝ)) ^ 2 - (690989 : ℝ) ^ 2 =
        3 * (690989 : ℝ) ^ 2 := by
  norm_num

end MathlibPlus.Arithmetic
