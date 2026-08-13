import Mathlib

namespace MathlibPlus.Analysis.Claim8643

open Matrix

/-- Claim 8643: the Jacobi transfer preserves its explicit quadratic form. -/
theorem invariantQuadraticForm_claim8643 {a x : ℝ} (ha : 0 < a) :
    let K : Matrix (Fin 2) (Fin 2) ℝ :=
      !![a⁻¹, -x / (2 * a); -x / (2 * a), a]
    let S : Matrix (Fin 2) (Fin 2) ℝ :=
      !![x / a, -a; 1 / a, 0]
    S.transpose * K * S = K := by
  dsimp
  have ha0 : a ≠ 0 := ne_of_gt ha
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha0] <;>
    field_simp [ha0] <;> ring

end MathlibPlus.Analysis.Claim8643
