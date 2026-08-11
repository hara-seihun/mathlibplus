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


/-- Claim 9198: the local theta increment has positive derivative on its natural
    domain.  The prime hypothesis is retained explicitly; the displayed
    expression uses `L = log q`. -/
theorem local_increment_derivative_pos_claim9198
    {q : ℕ} (hq : Nat.Prime q) {y : ℝ} (hy : 1 < y) :
    0 < 1 / (y * Real.log y) -
      1 / ((y + Real.log (q : ℝ)) * Real.log (y + Real.log (q : ℝ))) := by
  have hq2 : (1 : ℝ) < (q : ℝ) := by
    exact_mod_cast hq.one_lt
  have hL : 0 < Real.log (q : ℝ) := Real.log_pos hq2
  have hypos : 0 < y := by linarith
  have hsum : y < y + Real.log (q : ℝ) := by linarith
  have hsumpos : 0 < y + Real.log (q : ℝ) := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hlogsum : 0 < Real.log (y + Real.log (q : ℝ)) :=
    Real.log_pos (by linarith)
  have hlog_lt : Real.log y < Real.log (y + Real.log (q : ℝ)) := by
    exact Real.strictMonoOn_log hypos hsumpos hsum
  have ha : 0 < y * Real.log y := mul_pos hypos hlogy
  have hb : 0 < (y + Real.log (q : ℝ)) * Real.log (y + Real.log (q : ℝ)) :=
    mul_pos hsumpos hlogsum
  have hab : y * Real.log y <
      (y + Real.log (q : ℝ)) * Real.log (y + Real.log (q : ℝ)) := by
    nlinarith [mul_pos hypos hlogy, mul_pos hL hlogy,
      mul_pos hypos (sub_pos.mpr hlog_lt)]
  have hdiff : 0 <
      (y + Real.log (q : ℝ)) * Real.log (y + Real.log (q : ℝ)) -
        y * Real.log y := sub_pos.mpr hab
  have hprod : 0 <
      (y * Real.log y) *
        ((y + Real.log (q : ℝ)) * Real.log (y + Real.log (q : ℝ))) :=
    mul_pos ha hb
  have hformula :
      1 / (y * Real.log y) -
          1 / ((y + Real.log (q : ℝ)) * Real.log (y + Real.log (q : ℝ))) =
        (((y + Real.log (q : ℝ)) * Real.log (y + Real.log (q : ℝ))) -
          y * Real.log y) /
          ((y * Real.log y) *
            ((y + Real.log (q : ℝ)) * Real.log (y + Real.log (q : ℝ)))) := by
    field_simp [ne_of_gt ha, ne_of_gt hb]
  rw [hformula]
  exact div_pos hdiff hprod

end MathlibPlus.Analysis.LogarithmicBounds
