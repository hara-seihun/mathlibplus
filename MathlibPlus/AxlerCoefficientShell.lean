import MathlibPlus.AxlerMajorant

namespace MathlibPlus.AxlerMajorant

noncomputable section

/-- The common eight-term logarithmic majorant with free fifth, sixth, and
seventh inverse-log coefficients. -/
def coefficientShell (a5 a6 a7 x : ℝ) : ℝ :=
  let L := Real.log x
  x / L + x / L ^ 2 + 2 * x / L ^ 3 +
    (3012167 / 500000 : ℝ) * x / L ^ 4 +
    a5 * (x / L ^ 5) + a6 * (x / L ^ 6) + a7 * (x / L ^ 7) +
    (30486 / 5 : ℝ) * x / L ^ 8

/-- For `x > 1`, increasing any of the three free inverse-log coefficients
increases the common majorant. -/
theorem coefficientShell_mono
    (a5 a6 a7 b5 b6 b7 x : ℝ) (hx : 1 < x)
    (h5 : a5 ≤ b5) (h6 : a6 ≤ b6) (h7 : a7 ≤ b7) :
    coefficientShell a5 a6 a7 x ≤ coefficientShell b5 b6 b7 x := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hxpos : 0 ≤ x := le_of_lt (lt_trans (by norm_num) hx)
  have h5term : 0 ≤ x / Real.log x ^ 5 := by positivity
  have h6term : 0 ≤ x / Real.log x ^ 6 := by positivity
  have h7term : 0 ≤ x / Real.log x ^ 7 := by positivity
  have hdiff :
      coefficientShell b5 b6 b7 x - coefficientShell a5 a6 a7 x =
        (b5 - a5) * (x / Real.log x ^ 5) +
        (b6 - a6) * (x / Real.log x ^ 6) +
        (b7 - a7) * (x / Real.log x ^ 7) := by
    simp only [coefficientShell]
    ring
  have h5nonneg : 0 ≤ (b5 - a5) * (x / Real.log x ^ 5) :=
    mul_nonneg (sub_nonneg.mpr h5) h5term
  have h6nonneg : 0 ≤ (b6 - a6) * (x / Real.log x ^ 6) :=
    mul_nonneg (sub_nonneg.mpr h6) h6term
  have h7nonneg : 0 ≤ (b7 - a7) * (x / Real.log x ^ 7) :=
    mul_nonneg (sub_nonneg.mpr h7) h7term
  linarith

end

end MathlibPlus.AxlerMajorant
