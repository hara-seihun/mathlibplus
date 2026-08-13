import Mathlib

open scoped Matrix.Norms.Elementwise

namespace MathlibPlus.Analysis.Claim7589

/--
The explicit two-dimensional witness from claim 7589.  The matrix norm here is
Mathlib's elementwise supremum norm on matrices; the source claim leaves the
norm convention implicit, and this convention agrees with the displayed values
for this nilpotent witness.
-/
theorem positiveBranchWeights_notContractive_claim7589 (ω : ℝ) (hω : 0 < ω) :
    let T : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
    let D : Matrix (Fin 2) (Fin 2) ℝ := !![Real.exp ω, 0; 0, Real.exp (-ω)]
    let Dinv : Matrix (Fin 2) (Fin 2) ℝ := !![Real.exp (-ω), 0; 0, Real.exp ω]
    ‖T‖ = 1 ∧
      D * Dinv = 1 ∧
      Dinv * D = 1 ∧
      ‖D * T * Dinv‖ = Real.exp (2 * ω) ∧
      1 < Real.exp (2 * ω) := by
  let T : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
  let D : Matrix (Fin 2) (Fin 2) ℝ := !![Real.exp ω, 0; 0, Real.exp (-ω)]
  let Dinv : Matrix (Fin 2) (Fin 2) ℝ := !![Real.exp (-ω), 0; 0, Real.exp ω]
  dsimp only
  have hnormT : ‖T‖ = 1 := by
    apply le_antisymm
    · rw [Matrix.norm_le_iff (by norm_num)]
      intro i j
      fin_cases i <;> fin_cases j <;> simp [T]
    · have h := Matrix.norm_entry_le_entrywise_sup_norm T
          (i := (0 : Fin 2)) (j := (1 : Fin 2))
      simpa [T] using h
  have hDD : D * Dinv = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D, Dinv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, ← Real.exp_add]
  have hDinvD : Dinv * D = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D, Dinv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, ← Real.exp_add]
  have hconj : D * T * Dinv = !![0, Real.exp (2 * ω); 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [T, D, Dinv, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, ← Real.exp_add] <;> ring
  have hnormConj : ‖D * T * Dinv‖ = Real.exp (2 * ω) := by
    rw [hconj]
    apply le_antisymm
    · rw [Matrix.norm_le_iff (Real.exp_pos _).le]
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] <;> positivity
    · have h := Matrix.norm_entry_le_entrywise_sup_norm
          (!![0, Real.exp (2 * ω); 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
          (i := (0 : Fin 2)) (j := (1 : Fin 2))
      simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using h
  exact ⟨hnormT, hDD, hDinvD, hnormConj,
    by simpa using Real.exp_lt_exp.mpr (by linarith)⟩

end MathlibPlus.Analysis.Claim7589
