import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin

namespace MathlibPlus.Algebra.Claim17590

/-- Claim 17590: the elementary shear commutator has determinant one and
trace minus two equal to the squared product of its shear parameters. -/
theorem determinant_and_trace_of_shear_commutator {R : Type*} [CommRing R] (a b : R) :
    let U : R → Matrix (Fin 2) (Fin 2) R := fun t => !![1, t; 0, 1]
    let L : R → Matrix (Fin 2) (Fin 2) R := fun t => !![1, 0; t, 1]
    let C : Matrix (Fin 2) (Fin 2) R := U a * L b * U (-a) * L (-b)
    Matrix.det C = 1 ∧ Matrix.trace C - 2 = (a * b) ^ 2 := by
  dsimp
  have hC :
      (!![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) R) *
          !![1, 0; b, 1] *
          !![1, -a; 0, 1] *
          !![1, 0; -b, 1] =
        (!![1 + a * b + a ^ 2 * b ^ 2, -a ^ 2 * b;
            a * b ^ 2, 1 - a * b] : Matrix (Fin 2) (Fin 2) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  rw [hC]
  constructor
  · rw [Matrix.det_fin_two]
    norm_num
    ring
  · rw [Matrix.trace_fin_two]
    norm_num
    ring

end MathlibPlus.Algebra.Claim17590
