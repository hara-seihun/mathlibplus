import Mathlib

namespace MathlibPlus.LinearAlgebra

/--
Claim 11547.  The displayed split similitude has multiplier `9`, but its two
coordinate eigenvalues have moduli `2` and `9/2`, not the purity radius `3`.
The same matrix also fails the positive-identity similitude equation.
-/
theorem splitSimilitudeNotPure_claim11547 :
    let U : Matrix (Fin 2) (Fin 2) ℝ := !![(2 : ℝ), 0; 0, 9 / 2]
    let J : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
    let I : Matrix (Fin 2) (Fin 2) ℝ := 1
    let e₁ : Fin 2 → ℝ := ![1, 0]
    let e₂ : Fin 2 → ℝ := ![0, 1]
    Matrix.transpose U * J * U = 9 • J ∧
      Matrix.mulVec U e₁ = (2 : ℝ) • e₁ ∧
      Matrix.mulVec U e₂ = (9 / 2 : ℝ) • e₂ ∧
      ‖(2 : ℝ)‖ = 2 ∧ ‖(9 / 2 : ℝ)‖ = 9 / 2 ∧
      (2 : ℝ) ≠ 3 ∧ (9 / 2 : ℝ) ≠ 3 ∧
      Matrix.transpose U * I * U ≠ 9 • I := by
  dsimp
  have hsim :
      Matrix.transpose (!![(2 : ℝ), 0; 0, 9 / 2] : Matrix (Fin 2) (Fin 2) ℝ) *
          !![0, 1; 1, 0] *
          !![(2 : ℝ), 0; 0, 9 / 2] =
        9 • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  have he₁ :
      Matrix.mulVec (!![(2 : ℝ), 0; 0, 9 / 2] : Matrix (Fin 2) (Fin 2) ℝ)
          (![1, 0] : Fin 2 → ℝ) = (2 : ℝ) • (![1, 0] : Fin 2 → ℝ) := by
    funext i
    fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have he₂ :
      Matrix.mulVec (!![(2 : ℝ), 0; 0, 9 / 2] : Matrix (Fin 2) (Fin 2) ℝ)
          (![0, 1] : Fin 2 → ℝ) = (9 / 2 : ℝ) • (![0, 1] : Fin 2 → ℝ) := by
    funext i
    fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  refine ⟨hsim, he₁, he₂, ?_, ?_, by norm_num, by norm_num, ?_⟩
  · norm_num [Real.norm_eq_abs, abs_of_nonneg]
  · norm_num [Real.norm_eq_abs, abs_of_nonneg]
  · intro h
    have hentry := congr_fun (congr_fun h 0) 0
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ] at hentry

end MathlibPlus.LinearAlgebra
