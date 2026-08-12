import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim19257

/--
A positive-definite conditioning block gives the positive-semidefinite Schur
complement.  The explicit `fromBlocks` matrix retains the covariance block
matrix in the claim.
-/
theorem schurConditioningPreservesPosSemidef
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n n ℝ)
    (hC : C.PosDef) [Invertible C]
    (hblock : (Matrix.fromBlocks A B B.transpose C).PosSemidef) :
    (A - B * C⁻¹ * B.transpose).PosSemidef := by
  have h := (Matrix.PosDef.fromBlocks₂₂ A B hC).mp hblock
  simpa using h

end MathlibPlus.LinearAlgebra.Claim19257

