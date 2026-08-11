import Mathlib

namespace MathlibPlus.Algebra.GoldenRatio

/-- Claim 19954: the exact radical constant is the unique root in `(0, 1)`
of the displayed quadratic equation, and its reciprocal has the displayed
radical form. The source's terminating decimal prefix is only an approximation
and is therefore not asserted as an equality here. -/
theorem goldenRatioConstantIdentity :
    let α : ℝ := (3 - Real.sqrt 5) / 2
    0 < α ∧
      α < 1 ∧
      α = (1 - α) ^ 2 ∧
      (∀ p : ℝ, 0 < p → p < 1 → p = (1 - p) ^ 2 → p = α) ∧
      α⁻¹ = (3 + Real.sqrt 5) / 2 := by
  dsimp
  have hsqrt_sq : (Real.sqrt (5 : ℝ)) ^ 2 = 5 := by
    simpa using (Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num))
  have hsqrt_nonneg : 0 ≤ Real.sqrt (5 : ℝ) := Real.sqrt_nonneg _
  have hsqrt_lt_three : Real.sqrt (5 : ℝ) < 3 := by
    nlinarith
  have hα_pos : 0 < (3 - Real.sqrt 5) / 2 := by
    nlinarith
  have hα_lt_one : (3 - Real.sqrt 5) / 2 < 1 := by
    nlinarith
  have hα_eq : (3 - Real.sqrt 5) / 2 =
      (1 - (3 - Real.sqrt 5) / 2) ^ 2 := by
    nlinarith
  have hα_ne : (3 - Real.sqrt 5) / 2 ≠ 0 := ne_of_gt hα_pos
  have hprod :
      ((3 - Real.sqrt 5) / 2) * ((3 + Real.sqrt 5) / 2) = 1 := by
    nlinarith [hsqrt_sq]
  have hα_inv : ((3 - Real.sqrt 5) / 2)⁻¹ =
      (3 + Real.sqrt 5) / 2 := by
    calc
      ((3 - Real.sqrt 5) / 2)⁻¹ =
          ((3 - Real.sqrt 5) / 2)⁻¹ *
            (((3 - Real.sqrt 5) / 2) * ((3 + Real.sqrt 5) / 2)) := by
              rw [hprod, mul_one]
      _ = (((3 - Real.sqrt 5) / 2)⁻¹ *
            ((3 - Real.sqrt 5) / 2)) * ((3 + Real.sqrt 5) / 2) := by ring
      _ = (3 + Real.sqrt 5) / 2 := by
        rw [inv_mul_cancel₀ hα_ne, one_mul]
  refine ⟨hα_pos, hα_lt_one, hα_eq, ?_, hα_inv⟩
  intro p hp_pos hp_lt_one hp_eq
  have hp_quad : p ^ 2 - 3 * p + 1 = 0 := by
    nlinarith [hp_eq]
  have hfactor :
      (p - (3 - Real.sqrt 5) / 2) *
          (p - (3 + Real.sqrt 5) / 2) = 0 := by
    nlinarith [hp_quad, hsqrt_sq]
  rcases mul_eq_zero.mp hfactor with hroot | hother
  · linarith
  · have hother_gt_one : 1 < (3 + Real.sqrt 5) / 2 := by
      nlinarith
    linarith

end MathlibPlus.Algebra.GoldenRatio
