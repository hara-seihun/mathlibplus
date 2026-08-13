import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- Squaring the bipartite block lift gives the two Cholesky Gram blocks from
claim 8557.  The identity is purely algebraic, so it is stated for any
semiring and does not add positivity or irreducibility hypotheses. -/
theorem claim8557_bipartite_square_root_lift
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [Semiring R]
    (L : Matrix ι ι R) :
    let A : Matrix (ι ⊕ ι) (ι ⊕ ι) R := Matrix.fromBlocks 0 L L.transpose 0
    A ^ 2 = Matrix.fromBlocks (L * L.transpose) 0 0 (L.transpose * L) := by
  dsimp
  rw [pow_two, Matrix.fromBlocks_multiply]
  simp

end MathlibPlus.LinearAlgebra
