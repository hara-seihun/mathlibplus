import Mathlib

/-!
# Elementary facts for the false-RH curvature counterfeit
-/

namespace MathlibPlus.Analysis.FalseRHCurvature

/-- The displayed rational hyperbolic expression is strictly negative on the positive axis. -/
theorem curvatureExpression_neg {x : ℝ} (hx : 0 < x) :
    -(2 * (Real.cosh x - 1) * Real.sinh x) / (2 + Real.cosh x) ^ 3 < 0 := by
  have hcosh : 1 < Real.cosh x := Real.one_lt_cosh.mpr hx.ne'
  have hsinh : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  apply div_neg_of_neg_of_pos
  · exact neg_neg_of_pos (mul_pos (mul_pos (by norm_num) (sub_pos.mpr hcosh)) hsinh)
  · positivity

end MathlibPlus.Analysis.FalseRHCurvature
