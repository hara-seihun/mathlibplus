import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- The residual `4 × 4` block from the four delayed `D₁₂` fibers has the
nonzero determinant recorded in claim 23295. -/
theorem exactResidualDeterminant_claim23295 :
    let B : Matrix (Fin 4) (Fin 4) ℤ :=
      !![72, 0, 0, 0;
         0, 72, 0, 0;
         0, 0, 0, 144;
         0, 0, 144, 0]
    Matrix.det B = -(72 : ℤ)^2 * 144^2 ∧
      Matrix.det B = -107495424 ∧
      Matrix.det B = -(2^14 * 3^8 : ℤ) ∧
      Matrix.det B ≠ 0 := by
  decide

end MathlibPlus.LinearAlgebra
