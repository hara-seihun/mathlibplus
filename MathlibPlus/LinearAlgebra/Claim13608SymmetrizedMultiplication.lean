import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim13608

/-- Claim 13608: on Hermitian matrices, the symmetrized left/right
multiplication operator represents the trace quadratic form. -/
def symmetrized_multiplication_identity : Prop :=
  ∀ {n : Type*} [Fintype n]
    (M B : Matrix n n ℂ),
    M.IsHermitian → B.IsHermitian →
      (Matrix.trace (M * M * B)).re =
        (Matrix.trace (M.conjTranspose *
          ((1 / 2 : ℂ) • (B * M + M * B)))).re

end MathlibPlus.LinearAlgebra.Claim13608
