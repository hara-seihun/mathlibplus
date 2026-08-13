import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- Reindexing the columns of a square matrix by a permutation multiplies its
 determinant by the sign of that permutation. -/
theorem projectiveDeterminant_columnReindex_claim4965
    {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (M : Matrix n n R) (π : Equiv.Perm n) :
    (M.submatrix id π).det = (↑(Equiv.Perm.sign π) : R) * M.det := by
  have h := Matrix.det_permute π M.transpose
  rw [← Matrix.det_transpose M]
  rw [← Matrix.det_transpose (M.submatrix id π)]
  simpa [Matrix.transpose_submatrix] using h

end MathlibPlus.LinearAlgebra
