import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim12230

/--
The explicit hyperbolic block from claim 12230 preserves the split symmetric
form up to multiplier `9`, while its characteristic roots are `2` and `9/2`.
Thus the similitude identity does not force a common eigenvalue modulus.
-/
theorem splitDualityCounterexample :
    let J : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
    let U : Matrix (Fin 2) (Fin 2) ℝ := !![2, 0; 0, (9 : ℝ) / 2]
    let p : Polynomial ℝ :=
      Matrix.det ((Polynomial.X : Polynomial ℝ) •
        (1 : Matrix (Fin 2) (Fin 2) (Polynomial ℝ)) - U.map Polynomial.C)
    U.transpose * J * U = 9 • J ∧
      p = (Polynomial.X - Polynomial.C 2) *
        (Polynomial.X - Polynomial.C ((9 : ℝ) / 2)) ∧
      (∀ x : ℝ, p.eval x = 0 ↔
        x = 2 ∨ x = (9 : ℝ) / 2) ∧
      (∀ x : ℝ, p.eval x = 0 → |x| ≠ 3) := by
  dsimp
  have hsim :
      (!![2, 0; 0, (9 : ℝ) / 2] : Matrix (Fin 2) (Fin 2) ℝ).transpose *
          !![0, 1; 1, 0] *
          !![2, 0; 0, (9 : ℝ) / 2] =
        9 • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  have hpoly :
      Matrix.det ((Polynomial.X : Polynomial ℝ) •
          (1 : Matrix (Fin 2) (Fin 2) (Polynomial ℝ)) -
          (!![2, 0; 0, (9 : ℝ) / 2] : Matrix (Fin 2) (Fin 2) ℝ).map Polynomial.C) =
        (Polynomial.X - Polynomial.C 2) *
          (Polynomial.X - Polynomial.C ((9 : ℝ) / 2)) := by
    rw [Matrix.det_fin_two]
    simp [Matrix.sub_apply, Matrix.smul_apply]
  refine ⟨hsim, hpoly, ?_, ?_⟩
  · rw [hpoly]
    intro x
    constructor
    · intro hx
      have hfac : (x - 2) * (x - (9 : ℝ) / 2) = 0 := by
        simpa [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
          Polynomial.eval_X] using hx
      rcases mul_eq_zero.mp hfac with h | h
      · left
        linarith
      · right
        linarith
    · rintro (rfl | rfl) <;>
        simp [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
          Polynomial.eval_X]
  · rw [hpoly]
    intro x hx
    have hroot : x = 2 ∨ x = (9 : ℝ) / 2 := by
      have hfac : (x - 2) * (x - (9 : ℝ) / 2) = 0 := by
        simpa [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
          Polynomial.eval_X] using hx
      rcases mul_eq_zero.mp hfac with h | h
      · left
        linarith
      · right
        linarith
    rcases hroot with rfl | rfl <;> norm_num

end MathlibPlus.LinearAlgebra.Claim12230
