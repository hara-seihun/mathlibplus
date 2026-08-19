import Mathlib

namespace MathlibPlus.Analysis.ScalarLogarithmicMismatch

private lemma four_sinh_sq_log_half (x : ℝ) (hx : 0 < x) :
    4 * (Real.sinh (Real.log x / 2)) ^ 2 = (x - 1) ^ 2 / x := by
  let y : ℝ := Real.exp (Real.log x / 2)
  have hy : 0 < y := Real.exp_pos _
  have hysq : y ^ 2 = x := by
    dsimp [y]
    rw [pow_two, ← Real.exp_add]
    convert Real.exp_log hx using 1 <;> ring_nf
  rw [Real.sinh_eq, Real.exp_neg]
  change 4 * ((y - y⁻¹) / 2) ^ 2 = (x - 1) ^ 2 / x
  field_simp [ne_of_gt hy]
  rw [hysq]
  ring

private lemma sinh_sq_ge_sq (t : ℝ) :
    t ^ 2 ≤ (Real.sinh t) ^ 2 := by
  by_cases ht : 0 ≤ t
  · have h := Real.self_le_sinh_iff.mpr ht
    exact (sq_le_sq₀ ht (Real.sinh_nonneg_iff.mpr ht)).mpr h
  · have ht' : t ≤ 0 := le_of_not_ge ht
    have h := Real.sinh_le_self_iff.mpr ht'
    have hs : Real.sinh t ≤ 0 := Real.sinh_nonpos_iff.mpr ht'
    have h' : -t ≤ -Real.sinh t := neg_le_neg h
    have hsquare :=
      (sq_le_sq₀ (neg_nonneg.mpr ht') (neg_nonneg.mpr hs)).mpr h'
    simpa [neg_sq] using hsquare

/-- The scalar logarithmic mismatch inequality. -/
theorem scalar_logarithmic_mismatch_claim8603 (x : ℝ) (hx : 0 < x) :
    (Real.log x) ^ 2 ≤ (x - 1) ^ 2 / x := by
  calc
    (Real.log x) ^ 2 = 4 * (Real.log x / 2) ^ 2 := by ring
    _ ≤ 4 * (Real.sinh (Real.log x / 2)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left (sinh_sq_ge_sq _) (by norm_num)
    _ = (x - 1) ^ 2 / x := four_sinh_sq_log_half x hx

end MathlibPlus.Analysis.ScalarLogarithmicMismatch
