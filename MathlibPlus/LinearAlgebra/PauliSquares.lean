import Mathlib

namespace MathlibPlus.LinearAlgebra.PauliSquares

/--
Claim 4490, with the standard complex Pauli matrices made explicit.  The
second relation is the square of the scalar multiple `iY`.
-/
theorem pauliSquareRelations :
    let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
    let Y : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
    let Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
    X * X = 1 ∧
      (Complex.I • Y) * (Complex.I • Y) = -1 ∧
      Z * Z = 1 := by
  dsimp
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]

end MathlibPlus.LinearAlgebra.PauliSquares
