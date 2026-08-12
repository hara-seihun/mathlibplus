import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- The contiguous rank-`N` determinant flag from claim 17907.  The two
offsets select consecutive rows and columns of a doubly indexed kernel. -/
def contiguousDeterminantFlag_claim17907 {R : Type*} [CommRing R]
    (g : ℕ → ℕ → R) (N a b : ℕ) : R :=
  Matrix.det (fun i j : Fin N => g (a + (i : ℕ)) (b + (j : ℕ)))

end MathlibPlus.LinearAlgebra
