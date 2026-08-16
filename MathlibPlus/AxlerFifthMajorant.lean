import MathlibPlus.AxlerSixthMajorant

/-!
# Axler fifth-coefficient majorant

Exact coefficient-24 majorant and its comparison with the deduplicated C-0046
majorant, from Records 1 and 2 of source record `C-0048`. The packet's
prime-counting theorem and numerical certificates are not asserted here.
-/

namespace MathlibPlus.AxlerFifthMajorant

noncomputable section

/-- The packet's eight-term majorant with factorial fifth, sixth, and seventh
coefficients `24`, `120`, and `720`. -/
def fifthMajorant (x : ℝ) : ℝ :=
  let L := Real.log x
  x / L + x / L ^ 2 + 2 * x / L ^ 3 +
    (3012167 / 500000 : ℝ) * x / L ^ 4 +
    24 * x / L ^ 5 + 120 * x / L ^ 6 + 720 * x / L ^ 7 +
    (30486 / 5 : ℝ) * x / L ^ 8

/-- The exact pointwise reduction from the C-0046 majorant in Record 2. -/
theorem sixthMajorant_sub_fifthMajorant (x : ℝ) (hx : 1 < x) :
    MathlibPlus.AxlerSixthMajorant.sixthMajorant x - fifthMajorant x =
      (12167 / 500000 : ℝ) * x / Real.log x ^ 5 := by
  have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  simp only [MathlibPlus.AxlerSixthMajorant.sixthMajorant, fifthMajorant]
  field_simp [hlog]
  ring

/-- On the stated domain, the coefficient-24 majorant is strictly smaller than
C-0046's coefficient-24.024334 majorant. -/
theorem fifthMajorant_lt_sixthMajorant (x : ℝ) (hx : 1 < x) :
    fifthMajorant x < MathlibPlus.AxlerSixthMajorant.sixthMajorant x := by
  rw [← sub_pos]
  rw [sixthMajorant_sub_fifthMajorant x hx]
  have hxpos : 0 < x := lt_trans (by norm_num) hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  positivity

end

end MathlibPlus.AxlerFifthMajorant
