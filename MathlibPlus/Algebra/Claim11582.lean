import Mathlib

namespace MathlibPlus.Algebra.Claim11582

open Matrix

/-- The explicit split/alternating-duality counterexample from claim 11582. -/
theorem perfectDualityDoesNotImplyPurity_claim11582 :
    let M := Matrix (Fin 2) (Fin 2) ℝ
    let U : M := !![2, 0; 0, 9 / 2]
    let Js : M := !![0, 1; 1, 0]
    let Ja : M := !![0, 1; -1, 0]
    U.transpose * Js * U = 9 • Js ∧
      U.transpose * Ja * U = 9 • Ja ∧
      |U 0 0| = (2 : ℝ) ∧
      |U 1 1| = (9 / 2 : ℝ) ∧
      |U 0 0| ≠ (3 : ℝ) ∧
      |U 1 1| ≠ (3 : ℝ) ∧
      U.transpose * (1 : M) * U ≠ 9 • (1 : M) := by
  dsimp
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · intro h
    have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
    norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h00

end MathlibPlus.Algebra.Claim11582
