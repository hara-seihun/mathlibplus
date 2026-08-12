import Mathlib

set_option maxHeartbeats 1000000

namespace MathlibPlus.LinearAlgebra.Claim17573

noncomputable section

abbrev MatrixSpace (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- The source's `D`-isometry predicate. -/
def isDIsometry {n : ℕ} (D U : MatrixSpace n) : Prop :=
  Matrix.transpose U * D * U = D

/-- The skew/Plücker channel from two `D`-isometries. -/
def skewPluckerChannel {n : ℕ} (D U V : MatrixSpace n) : MatrixSpace n :=
  (1 / 2 : ℝ) •
    (Matrix.transpose V * D * U - Matrix.transpose U * D * V)

/-- The displayed channel is skew when the form matrix is symmetric. -/
theorem skewPluckerChannel_transpose {n : ℕ}
    (D U V : MatrixSpace n)
    (hD : Matrix.transpose D = D)
    (_hU : isDIsometry D U) (_hV : isDIsometry D V) :
    Matrix.transpose (skewPluckerChannel D U V) =
      -skewPluckerChannel D U V := by
  unfold skewPluckerChannel
  simp only [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_mul,
    Matrix.transpose_transpose, hD]
  simp [smul_sub, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    Matrix.mul_assoc]

end

end MathlibPlus.LinearAlgebra.Claim17573
