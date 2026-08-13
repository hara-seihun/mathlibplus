import Mathlib

namespace MathlibPlus.LinearAlgebra

/--
Claim 4945.  Multiplying every column of a rank-`r` square matrix by two
multiplies its determinant by `2^r`; this is the source-independent
folded-versus-centered determinant scaling core.
-/
theorem foldedEvenJetDeterminantScaling_claim4945
    {R : Type*} [CommRing R] (r : ℕ) (M : Matrix (Fin r) (Fin r) R) :
    Matrix.det (fun i j => (2 : R) * M i j) =
      (2 : R) ^ r * Matrix.det M := by
  have hmatrix :
      (fun i j => (2 : R) * M i j) = (2 : R) • M := by
    ext i j
    simp [smul_eq_mul]
  rw [hmatrix, Matrix.det_smul]
  simp

end MathlibPlus.LinearAlgebra
