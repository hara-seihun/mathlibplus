import Mathlib

/-!
# Axler factorial-720 majorant

Exact majorant definitions and the same-eighth-coefficient comparison from Records
2 and 4 of legacy extraction bundle `C-0044`. The packet's prime-counting theorem
and numerical certificates are not asserted here.
-/

namespace MathlibPlus.AxlerMajorant

noncomputable section

/-- The packet's eight-term majorant with factorial seventh coefficient `720`. -/
def factorial720Bound (x : ℝ) : ℝ :=
  let L := Real.log x
  x / L + x / L ^ 2 + 2 * x / L ^ 3 +
    (3012167 / 500000 : ℝ) * x / L ^ 4 +
    (12012167 / 500000 : ℝ) * x / L ^ 5 +
    (12012167 / 100000 : ℝ) * x / L ^ 6 +
    720 * x / L ^ 7 + (30486 / 5 : ℝ) * x / L ^ 8

/-- The packet's predecessor majorant, differing only in its seventh coefficient. -/
def predecessorBound (x : ℝ) : ℝ :=
  let L := Real.log x
  x / L + x / L ^ 2 + 2 * x / L ^ 3 +
    (3012167 / 500000 : ℝ) * x / L ^ 4 +
    (12012167 / 500000 : ℝ) * x / L ^ 5 +
    (12012167 / 100000 : ℝ) * x / L ^ 6 +
    (36036501 / 50000 : ℝ) * x / L ^ 7 +
    (30486 / 5 : ℝ) * x / L ^ 8

/-- The exact pointwise reduction in Record 4. -/
theorem predecessor_sub_factorial720 (x : ℝ) (hx : 1 < x) :
    predecessorBound x - factorial720Bound x =
      (36501 / 50000 : ℝ) * x / Real.log x ^ 7 := by
  have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  simp only [predecessorBound, factorial720Bound]
  field_simp [hlog]
  ring

/-- On the stated domain, the factorial-720 right-hand side is strictly smaller
than the predecessor right-hand side. -/
theorem factorial720Bound_lt_predecessorBound (x : ℝ) (hx : 1 < x) :
    factorial720Bound x < predecessorBound x := by
  rw [← sub_pos]
  rw [predecessor_sub_factorial720 x hx]
  have hxpos : 0 < x := lt_trans (by norm_num) hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  positivity

end

end MathlibPlus.AxlerMajorant
