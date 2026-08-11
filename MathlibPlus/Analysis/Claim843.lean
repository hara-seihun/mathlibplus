import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim843

/-- The two explicit same-shape denominators are ordered by their exact
coefficients; positivity of both denominators then gives the strict quotient
comparison. -/
theorem strictSameShapeComparison (x : ℝ) (hx : 29.53 ≤ x)
    (h44 : 0 < Real.log x - 1 - (Real.log x)⁻¹ -
      3 / (Real.log x) ^ 2 - 44.053 / (Real.log x) ^ 3)
    (h70 : 0 < Real.log x - 1 - (Real.log x)⁻¹ -
      3 / (Real.log x) ^ 2 - 70.935 / (Real.log x) ^ 3) :
    x / (Real.log x - 1 - (Real.log x)⁻¹ -
        3 / (Real.log x) ^ 2 - 44.053 / (Real.log x) ^ 3) <
      x / (Real.log x - 1 - (Real.log x)⁻¹ -
        3 / (Real.log x) ^ 2 - 70.935 / (Real.log x) ^ 3) := by
  have hxpos : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog3 : 0 < (Real.log x) ^ 3 := by positivity
  let d44 : ℝ := Real.log x - 1 - (Real.log x)⁻¹ -
    3 / (Real.log x) ^ 2 - 44.053 / (Real.log x) ^ 3
  let d70 : ℝ := Real.log x - 1 - (Real.log x)⁻¹ -
    3 / (Real.log x) ^ 2 - 70.935 / (Real.log x) ^ 3
  have horder : d70 < d44 := by
    have hdiff : d44 - d70 = (70.935 - 44.053 : ℝ) / (Real.log x) ^ 3 := by
      dsimp [d44, d70]
      field_simp [ne_of_gt hlog]
      ring
    have hgap : 0 < (70.935 - 44.053 : ℝ) / (Real.log x) ^ 3 :=
      div_pos (by norm_num) hlog3
    nlinarith [hdiff]
  change x / d44 < x / d70
  apply (div_lt_div_iff₀ h44 h70).2
  exact mul_lt_mul_of_pos_left horder hxpos

end MathlibPlus.Analysis.Claim843
