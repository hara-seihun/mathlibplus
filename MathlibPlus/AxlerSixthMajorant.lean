import MathlibPlus.AxlerMajorant

/-!
# Axler sixth-coefficient majorant

Exact coefficient-120 majorant and its comparison with the deduplicated C-0044
majorant, from Records 1 and 4 of legacy extraction bundle `C-0046`. The packet's
prime-counting theorem and numerical certificates are not asserted here.
-/

namespace MathlibPlus.AxlerSixthMajorant

noncomputable section

/-- The packet's eight-term majorant with factorial sixth and seventh coefficients
`120` and `720`. -/
def sixthMajorant (x : ℝ) : ℝ :=
  let L := Real.log x
  x / L + x / L ^ 2 + 2 * x / L ^ 3 +
    (3012167 / 500000 : ℝ) * x / L ^ 4 +
    (12012167 / 500000 : ℝ) * x / L ^ 5 +
    120 * x / L ^ 6 + 720 * x / L ^ 7 +
    (30486 / 5 : ℝ) * x / L ^ 8

/-- The exact pointwise reduction from the C-0044 majorant in Record 4. -/
theorem sixthMajorant_eq_factorial720Bound_sub (x : ℝ) (hx : 1 < x) :
    sixthMajorant x = MathlibPlus.AxlerMajorant.factorial720Bound x -
      (12167 / 100000 : ℝ) * x / Real.log x ^ 6 := by
  have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  simp only [sixthMajorant, MathlibPlus.AxlerMajorant.factorial720Bound]
  field_simp [hlog]
  ring

/-- On the stated domain, the coefficient-120 majorant is strictly smaller than
C-0044's coefficient-120.12167 majorant. -/
theorem sixthMajorant_lt_factorial720Bound (x : ℝ) (hx : 1 < x) :
    sixthMajorant x < MathlibPlus.AxlerMajorant.factorial720Bound x := by
  rw [sixthMajorant_eq_factorial720Bound_sub x hx]
  have hxpos : 0 < x := lt_trans (by norm_num) hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hterm : 0 < (12167 / 100000 : ℝ) * x / Real.log x ^ 6 := by positivity
  linarith

end

end MathlibPlus.AxlerSixthMajorant
