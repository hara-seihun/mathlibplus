import Mathlib.LinearAlgebra.Matrix.PosDef

namespace MathlibPlus.LinearAlgebra.ExplicitFrobeniusSimilitude

noncomputable section

open Matrix

/-! Formalization of admitted claim 11543. -/

/-- The displayed symmetric form has determinant `11/4`. -/
theorem similitudeForm_det :
    Matrix.det
        (!![1, -(3 : ℝ) / 2; -(3 : ℝ) / 2, 5] : Matrix (Fin 2) (Fin 2) ℝ) =
      (11 : ℝ) / 4 := by
  norm_num [Matrix.det_fin_two]

/-- The displayed Frobenius matrix is a similitude of the displayed form. -/
theorem frobeniusMatrix_transpose_mul_form_mul :
    let F : Matrix (Fin 2) (Fin 2) ℝ := !![0, -5; 1, -3]
    let P : Matrix (Fin 2) (Fin 2) ℝ := !![1, -(3 : ℝ) / 2; -(3 : ℝ) / 2, 5]
    F.transpose * P * F = 5 • P := by
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

/-- The displayed symmetric form is positive definite. -/
theorem similitudeForm_posDef :
    let P : Matrix (Fin 2) (Fin 2) ℝ := !![1, -(3 : ℝ) / 2; -(3 : ℝ) / 2, 5]
    P.PosDef := by
  dsimp
  let P : Matrix (Fin 2) (Fin 2) ℝ := !![1, -(3 : ℝ) / 2; -(3 : ℝ) / 2, 5]
  change P.PosDef
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, Matrix.IsHermitian, starRingEnd_apply]
  · intro x hx0
    have hx : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      have h0 : x 0 = 0 := by
        by_contra h0
        exact h (Or.inl h0)
      have h1 : x 1 = 0 := by
        by_contra h1
        exact h (Or.inr h1)
      have hxzero : x = 0 := by
        funext i
        fin_cases i <;> assumption
      exact hx0 hxzero
    simp [P, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
    have hform :
        x 0 * (x 0 + -3 / 2 * x 1) + x 1 * (-3 / 2 * x 0 + 5 * x 1) =
          (x 0 - (3 / 2 : ℝ) * x 1) ^ 2 + (11 / 4 : ℝ) * (x 1) ^ 2 := by
      ring
    rw [hform]
    rcases hx with hx | hx
    · by_cases h1 : x 1 = 0
      · simpa [h1] using (sq_pos_of_ne_zero hx)
      · exact add_pos_of_nonneg_of_pos (sq_nonneg _)
          (mul_pos (by norm_num) (sq_pos_of_ne_zero h1))
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _)
        (mul_pos (by norm_num) (sq_pos_of_ne_zero hx))

end

end MathlibPlus.LinearAlgebra.ExplicitFrobeniusSimilitude
