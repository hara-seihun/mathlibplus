import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim46084

/-!
Formalization of the explicit hostile finite example in admitted claim 46084.
The source's general total-nonnegativity/compound criterion is not encoded
because the claim record does not define those interfaces; the displayed
transition minors, row recurrence, stacked matrix, and negative stack minor
are retained exactly.
-/

/-- The two displayed transitions have positive maximal minors, but their
zero-padded row stack has the displayed negative `2 × 2` minor. -/
theorem hostileTransitionExample :
    let T1 : Matrix (Fin 1) (Fin 2) ℝ := !![1, 10]
    let T2 : Matrix (Fin 2) (Fin 3) ℝ := !![1, 2, 3; 1, 3, 5]
    let r0 : Fin 1 → ℝ := ![1]
    let r1 : Fin 2 → ℝ := Matrix.vecMul r0 T1
    let r2 : Fin 3 → ℝ := Matrix.vecMul r1 T2
    let A : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
      if i = 0 then if j = 0 then r0 0 else 0
      else if i = 1 then if j = 0 then r1 0 else if j = 1 then r1 1 else 0
      else if j = 0 then r2 0 else if j = 1 then r2 1 else r2 2
    0 < T1 0 0 ∧ 0 < T1 0 1 ∧
      0 < (T2 0 0 * T2 1 1 - T2 0 1 * T2 1 0) ∧
      0 < (T2 0 0 * T2 1 2 - T2 0 2 * T2 1 0) ∧
      0 < (T2 0 1 * T2 1 2 - T2 0 2 * T2 1 1) ∧
      A = !![1, 0, 0; 1, 10, 0; 11, 32, 53] ∧
      (A 1 0 * A 2 1 - A 1 1 * A 2 0 : ℝ) = -78 := by
  dsimp
  norm_num [Matrix.vecMul, Fin.sum_univ_succ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.vecMul, Fin.sum_univ_succ] <;> norm_num

end MathlibPlus.LinearAlgebra.Claim46084
