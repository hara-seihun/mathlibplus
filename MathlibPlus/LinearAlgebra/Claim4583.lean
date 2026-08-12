import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim4583

/-- The completed Bezout matrix from the factorial-moment packet.  The finite
range is the displayed `0 ≤ a ≤ min(i,j)` range, with moments zero-extended
implicitly by the supplied sequence `h`. -/
def completedBezoutMatrix_claim4583 (N : ℕ) (h : ℕ → ℚ) :
    Matrix (Fin N) (Fin N) ℚ := fun i j =>
      ∑ a ∈ Finset.range (min (i : ℕ) (j : ℕ) + 1),
        (((i : ℕ) + (j : ℕ) + 1 - 2 * a : ℕ) : ℚ) * h a *
          h ((i : ℕ) + (j : ℕ) + 1 - a)

/-- Rank four is the matrix used by the source packet. -/
def completedBezoutMatrix4_claim4583 (h : ℕ → ℚ) :
    Matrix (Fin 4) (Fin 4) ℚ := completedBezoutMatrix_claim4583 4 h

theorem completedBezoutMatrix_entry_claim4583 (N : ℕ) (h : ℕ → ℚ)
    (i j : Fin N) :
    completedBezoutMatrix_claim4583 N h i j =
      ∑ a ∈ Finset.range (min (i : ℕ) (j : ℕ) + 1),
        (((i : ℕ) + (j : ℕ) + 1 - 2 * a : ℕ) : ℚ) * h a *
          h ((i : ℕ) + (j : ℕ) + 1 - a) := by
  rfl

end MathlibPlus.LinearAlgebra.Claim4583
