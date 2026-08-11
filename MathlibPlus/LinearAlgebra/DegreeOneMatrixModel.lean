import Mathlib

namespace MathlibPlus.LinearAlgebra.DegreeOneMatrixModel

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- The matrix `X` in the degree-one model. -/
def X : Mat2 := !![0, 1; 1, 0]

/-- The transpose map `S₁`. -/
def S_one (M : Mat2) : Mat2 := M.transpose

/-- Left multiplication by `X`. -/
def R_h (M : Mat2) : Mat2 := X * M

/-- Right multiplication by `X`. -/
def R_c (M : Mat2) : Mat2 := M * X

/-- The conjugation map displayed in the packet. -/
def D (M : Mat2) : Mat2 := X * M * X

/-- The square of transpose after left multiplication by `X`. -/
def transposeCompLX (M : Mat2) : Mat2 := (X * M).transpose

/-- Conjugation by the involution `X`. -/
def Ad_X (M : Mat2) : Mat2 := X * M * X

/-- The matrix-side identities in the degree-one model. -/
theorem degreeOneMatrixModel (M : Mat2) :
    S_one M = M.transpose ∧
      R_h M = X * M ∧
      R_c M = M * X ∧
      D M = X * M * X := by
  simp [S_one, R_h, R_c, D]

/-- Since `X` is symmetric and involutive, the square of `transpose ∘ L_X`
is conjugation by `X`. -/
theorem transposeCompLX_sq_eq_Ad_X (M : Mat2) :
    transposeCompLX (transposeCompLX M) = Ad_X M := by
  classical
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transposeCompLX, Ad_X, Matrix.transpose_apply, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two, X]

end MathlibPlus.LinearAlgebra.DegreeOneMatrixModel
