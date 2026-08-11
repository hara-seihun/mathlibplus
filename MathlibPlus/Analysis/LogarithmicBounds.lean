import MathlibPlus.Basic

namespace MathlibPlus.Analysis.LogarithmicBounds

/-!
Formalization of admitted claim 11856.  The source gives no tail index set,
convergence hypothesis, or numerical tail bound, so the explicit universal
inequalities are stated without inventing a product application.
-/

/-- The logarithm has the standard reciprocal lower bound on `(0, 1)`. -/
theorem log_one_sub_ge_neg_div {u : ℝ} (_hu0 : 0 < u) (hu1 : u < 1) :
    Real.log (1 - u) ≥ -u / (1 - u) := by
  have hpos : 0 < 1 - u := sub_pos.mpr hu1
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at h
  have hrewrite : (1 - u)⁻¹ - 1 = u / (1 - u) := by
    field_simp
    ring
  rw [hrewrite] at h
  calc
    -u / (1 - u) = -(u / (1 - u)) := by ring
    _ ≤ Real.log (1 - u) := by simpa using (neg_le_neg h)

/-- The tangent-line lower bound for the negative exponential. -/
theorem exp_neg_ge_one_sub (x : ℝ) : 1 - x ≤ Real.exp (-x) := by
  have h := Real.add_one_le_exp (-x)
  linarith

end MathlibPlus.Analysis.LogarithmicBounds
