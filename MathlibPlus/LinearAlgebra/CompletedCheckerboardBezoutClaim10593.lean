import MathlibPlus.LinearAlgebra.CompletedBezout

namespace MathlibPlus.LinearAlgebra.CompletedBezout

/-- Claim 10593's checkerboard formula is exactly the canonical completed-Bezout
matrix and its determinant. -/
theorem completedCheckerboardBezout_claim10593 (m : ℕ → ℝ) (N : ℕ) :
    (∀ i j : Fin N,
      completedBezoutMatrix m N i j =
        ∑ a ∈ Finset.range (min (i : ℕ) (j : ℕ) + 1),
          ((i.1 + j.1 + 1 - 2 * a : ℕ) : ℝ) * m a *
            m (i.1 + j.1 + 1 - a)) ∧
      completedBezoutDeterminant m N =
        Matrix.det (completedBezoutMatrix m N) := by
  refine ⟨?_, rfl⟩
  intro i j
  exact completedBezoutMatrix_apply m N i j

end MathlibPlus.LinearAlgebra.CompletedBezout
