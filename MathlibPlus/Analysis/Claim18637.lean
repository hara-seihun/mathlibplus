import Mathlib

namespace MathlibPlus.Analysis.Claim18637

/-- The boundary-layer second Wronskian is positive on the positive half-line.
The source's `sech` is written as `1 / cosh`, since mathlib has no separate
`sech` function. -/
theorem secondWronskian_pos_claim18637 (Q : ℝ) (hQ : 0 < Q) :
    0 < 2 * (Real.tanh Q - Q / (Real.cosh Q) ^ 2 +
      2 * Q ^ 2 / (Real.cosh Q) ^ 2 * Real.tanh Q) := by
  have hcosh : 0 < Real.cosh Q := Real.cosh_pos Q
  have hcosh2 : 0 < (Real.cosh Q) ^ 2 := sq_pos_of_pos hcosh
  have hsinh : 0 < Real.sinh Q := (Real.sinh_pos_iff).2 hQ
  have htanh : 0 < Real.tanh Q := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos hsinh hcosh
  have htwice : 2 * Q < Real.sinh (2 * Q) := by
    exact Real.self_lt_sinh_iff.2 (by linarith)
  rw [Real.sinh_two_mul] at htwice
  have hprod : Q < Real.sinh Q * Real.cosh Q := by
    nlinarith
  have hbase : 0 < Real.tanh Q - Q / (Real.cosh Q) ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    have heq : Real.sinh Q / Real.cosh Q - Q / (Real.cosh Q) ^ 2 =
        (Real.sinh Q * Real.cosh Q - Q) / (Real.cosh Q) ^ 2 := by
      field_simp [ne_of_gt hcosh]
    rw [heq]
    exact div_pos (sub_pos.mpr hprod) hcosh2
  have hsecond : 0 < 2 * Q ^ 2 / (Real.cosh Q) ^ 2 * Real.tanh Q := by
    exact mul_pos (div_pos (mul_pos (by norm_num) (sq_pos_of_pos hQ)) hcosh2) htanh
  exact mul_pos (by norm_num) (add_pos hbase hsecond)

end MathlibPlus.Analysis.Claim18637
