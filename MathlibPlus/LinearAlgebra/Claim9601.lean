import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim9601

/-- The six-by-four Radon incidence matrix has the displayed Gram matrix,
    determinant 48, and full column rank. -/
theorem radonMatrixGramDeterminant_rank :
    let A : Matrix (Fin 6) (Fin 4) ℚ :=
      !![1, 1, 0, 0;
         1, 0, 1, 0;
         1, 0, 0, 1;
         0, 1, 1, 0;
         0, 1, 0, 1;
         0, 0, 1, 1]
    let G := A.transpose * A
    (∀ i : Fin 4, G i i = 3) ∧
      (∀ i j : Fin 4, i ≠ j → G i j = 1) ∧
      G.det = 48 ∧ A.rank = 4 := by
  let A : Matrix (Fin 6) (Fin 4) ℚ :=
    !![1, 1, 0, 0;
       1, 0, 1, 0;
       1, 0, 0, 1;
       0, 1, 1, 0;
       0, 1, 0, 1;
       0, 0, 1, 1]
  change
    (∀ i : Fin 4, (A.transpose * A) i i = 3) ∧
      (∀ i j : Fin 4, i ≠ j → (A.transpose * A) i j = 1) ∧
      (A.transpose * A).det = 48 ∧ A.rank = 4
  have hgram : A.transpose * A =
      (!![3, 1, 1, 1;
          1, 3, 1, 1;
          1, 1, 3, 1;
          1, 1, 1, 3] : Matrix (Fin 4) (Fin 4) ℚ) := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals norm_num [A, Matrix.mul_apply, Fin.sum_univ_succ]
  have hdiag : ∀ i : Fin 4, (A.transpose * A) i i = 3 := by
    intro i
    rw [hgram]
    fin_cases i <;> norm_num
  have hoff : ∀ i j : Fin 4, i ≠ j → (A.transpose * A) i j = 1 := by
    intro i j hij
    rw [hgram]
    fin_cases i <;> fin_cases j <;> simp_all
  have detFinFour : ∀ (M : Matrix (Fin 4) (Fin 4) ℚ),
      M.det =
        M 0 0 * (M 1 1 * M 2 2 * M 3 3 - M 1 1 * M 2 3 * M 3 2 -
          M 1 2 * M 2 1 * M 3 3 + M 1 2 * M 2 3 * M 3 1 +
          M 1 3 * M 2 1 * M 3 2 - M 1 3 * M 2 2 * M 3 1) -
        M 0 1 * (M 1 0 * M 2 2 * M 3 3 - M 1 0 * M 2 3 * M 3 2 -
          M 1 2 * M 2 0 * M 3 3 + M 1 2 * M 2 3 * M 3 0 +
          M 1 3 * M 2 0 * M 3 2 - M 1 3 * M 2 2 * M 3 0) +
        M 0 2 * (M 1 0 * M 2 1 * M 3 3 - M 1 0 * M 2 3 * M 3 1 -
          M 1 1 * M 2 0 * M 3 3 + M 1 1 * M 2 3 * M 3 0 +
          M 1 3 * M 2 0 * M 3 1 - M 1 3 * M 2 1 * M 3 0) -
        M 0 3 * (M 1 0 * M 2 1 * M 3 2 - M 1 0 * M 2 2 * M 3 1 -
          M 1 1 * M 2 0 * M 3 2 + M 1 1 * M 2 2 * M 3 0 +
          M 1 2 * M 2 0 * M 3 1 - M 1 2 * M 2 1 * M 3 0) := by
    intro M
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
    simp (discharger := decide) [Matrix.det_fin_three, Fin.succAbove]
    ring
  have hdet : (A.transpose * A).det = 48 := by
    rw [hgram, detFinFour]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]
    norm_num
  have hdet_ne : (A.transpose * A).det ≠ 0 := by
    rw [hdet]
    norm_num
  have hgramrank : (A.transpose * A).rank = 4 := by
    simpa using (Matrix.rank_of_det_ne_zero hdet_ne)
  have hlow : 4 ≤ A.rank := by
    calc
      4 = (A.transpose * A).rank := hgramrank.symm
      _ ≤ A.transpose.rank := Matrix.rank_mul_le_left A.transpose A
      _ = A.rank := Matrix.rank_transpose A
  have hupp : A.rank ≤ 4 := by
    simpa using (Matrix.rank_le_width A)
  exact ⟨hdiag, hoff, hdet, le_antisymm hupp hlow⟩

end MathlibPlus.LinearAlgebra.Claim9601
