import Mathlib

/-!
# Two-dimensional alternating similitude

The matrix identity from admitted claim 12306 is stated over an arbitrary
commutative ring, the exact algebraic scope of the determinant calculation.
-/

namespace MathlibPlus.LinearAlgebra

/-- Every two-by-two matrix preserves the standard alternating form up to its
 determinant. -/
theorem twoDimensionalAlternatingSimilitude {R : Type*} [CommRing R]
    (A : Matrix (Fin 2) (Fin 2) R) :
    A.transpose * !![0, 1; -1, 0] * A =
      Matrix.det A • (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

end MathlibPlus.LinearAlgebra
