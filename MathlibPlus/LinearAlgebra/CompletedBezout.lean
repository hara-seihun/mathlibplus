import Mathlib

/-!
# Completed Bezout matrices

The finite matrix and determinant used by the completed-Bezout hierarchy.
-/

namespace MathlibPlus.LinearAlgebra.CompletedBezout

open scoped BigOperators

/-- The rank-`N` completed Bezout matrix associated with the coefficient sequence
`h`, with indices starting at zero. -/
noncomputable def completedBezoutMatrix
    (h : ℕ → ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    ∑ a ∈ Finset.range (min (i : ℕ) (j : ℕ) + 1),
      ((i.1 + j.1 + 1 - 2 * a : ℕ) : ℝ) * h a * h (i.1 + j.1 + 1 - a)

/-- The rank-`N` completed Bezout determinant. -/
noncomputable def completedBezoutDeterminant
    (h : ℕ → ℝ) (N : ℕ) : ℝ :=
  Matrix.det (completedBezoutMatrix h N)

/-- Entrywise expansion of the completed Bezout matrix. -/
theorem completedBezoutMatrix_apply
    (h : ℕ → ℝ) (N : ℕ) (i j : Fin N) :
    completedBezoutMatrix h N i j =
      ∑ a ∈ Finset.range (min (i : ℕ) (j : ℕ) + 1),
        ((i.1 + j.1 + 1 - 2 * a : ℕ) : ℝ) * h a * h (i.1 + j.1 + 1 - a) := by
  rfl

end MathlibPlus.LinearAlgebra.CompletedBezout
