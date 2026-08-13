import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim17076

/-- A balanced signed adjacency matrix annihilates the constant vector. -/
theorem signedAdjacency_mul_one_eq_zero {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℝ) (hrow : ∀ i, ∑ j, H i j = 0) :
    Matrix.mulVec H (fun _ : ι => (1 : ℝ)) = 0 := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  simpa using hrow i

end MathlibPlus.LinearAlgebra.Claim17076
