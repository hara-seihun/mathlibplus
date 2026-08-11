import Mathlib

namespace MathlibPlus.Algebra.QuadraticMomentMultiplication

variable {R : Type*} [CommRing R]
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

/--
Formalization of admitted claim 26261.  The source leaves the matrix sizes and
coefficient system implicit; this states the same multiplication identity for
arbitrary finite index types over a commutative ring.
-/
theorem quadraticMomentMultiplication (D : Matrix n m R) (w : m → R) (c : n → R)
    (h : D * Matrix.diagonal w * D.transpose = 0) :
    Matrix.mulVec D
        (Matrix.mulVec (Matrix.diagonal (Matrix.mulVec D.transpose c)) w) = 0 := by
  have hv :
      Matrix.mulVec (Matrix.diagonal (Matrix.mulVec D.transpose c)) w =
        Matrix.mulVec (Matrix.diagonal w) (Matrix.mulVec D.transpose c) := by
    funext j
    rw [Matrix.mulVec_diagonal, Matrix.mulVec_diagonal]
    exact mul_comm _ _
  rw [hv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]
  simp

end MathlibPlus.Algebra.QuadraticMomentMultiplication
