import MathlibPlus.LinearAlgebra.CompletedBezout

namespace MathlibPlus.LinearAlgebra.Claim17893

open MathlibPlus.LinearAlgebra.CompletedBezout

/-- The exact rank-two completed-Bezout determinant in coefficient coordinates. -/
theorem rankTwoCompletedBezoutDeterminant (h : ℕ → ℝ) :
    (completedBezoutMatrix h 2).det =
      h 0 * h 1 * (h 1 * h 2 + 3 * h 0 * h 3) -
        4 * h 0 ^ 2 * h 2 ^ 2 := by
  rw [Matrix.det_fin_two]
  simp [completedBezoutMatrix, Finset.sum_range_succ]
  ring

end MathlibPlus.LinearAlgebra.Claim17893
