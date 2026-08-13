import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra

/--
The determinant and symmetry part of admitted claim 47538.  An invertible
congruence preserves the strict sign of a symmetric form's determinant.
-/
theorem claim47538_symmetric_congruence
    {n : ℕ} (S M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsSymm) (hS : Not ((S.det) = 0)) (hneg : (M.det < 0)) :
    (S.transpose * M * S).IsSymm ∧
      Matrix.det (S.transpose * M * S) = Matrix.det S ^ 2 * Matrix.det M ∧
        Matrix.det (S.transpose * M * S) < 0 := by
  have hsymm : (S.transpose * M * S).IsSymm := by
    rw [Matrix.IsSymm]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hM.eq]
    rw [Matrix.mul_assoc]
  have hdet :
      Matrix.det (S.transpose * M * S) = Matrix.det S ^ 2 * Matrix.det M := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hsquare : 0 < Matrix.det S ^ 2 := sq_pos_of_ne_zero hS
  refine ⟨hsymm, hdet, ?_⟩
  rw [hdet]
  exact mul_neg_of_pos_of_neg hsquare hneg

end MathlibPlus.LinearAlgebra
