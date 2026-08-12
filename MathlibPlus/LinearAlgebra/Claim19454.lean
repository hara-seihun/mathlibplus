import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim19454

open Matrix

/--
A concrete square (hence rectangular) reflection witness: the Gram matrix is
unchanged while the oriented maximal minor, here the determinant, changes sign.
-/
theorem gramCollisionWithOrientedMinor_claim19454 :
    ∃ B₁ B₂ : Matrix (Fin 2) (Fin 2) ℝ,
      B₁ * B₁.transpose = B₂ * B₂.transpose ∧
        Matrix.det B₁ ≠ Matrix.det B₂ := by
  let Q : Matrix (Fin 2) (Fin 2) ℝ :=
    Matrix.diagonal (fun i => if i = 0 then (-1 : ℝ) else 1)
  refine ⟨(1 : Matrix (Fin 2) (Fin 2) ℝ), Q, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Q, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]
  · norm_num [Q, Matrix.det_diagonal]

end MathlibPlus.LinearAlgebra.Claim19454
