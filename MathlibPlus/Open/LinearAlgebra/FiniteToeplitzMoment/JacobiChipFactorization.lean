import Mathlib

namespace MathlibPlus.Open.LinearAlgebra.FiniteToeplitzMoment

/-- The lower triangular Toeplitz matrix with parameter `z`. -/
def toeplitzMatrix (N : ℕ) (z : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun a b => if b.val ≤ a.val then z ^ (a.val - b.val) else 0

/-- The elementary matrix having a single `1` at `(i, j)`. -/
def elementaryMatrix {N : ℕ} (i j : Fin N) : Matrix (Fin N) (Fin N) ℝ :=
  fun a b => if a = i ∧ b = j then 1 else 0

/-- The factor indexed by `k` is `I + z E_(k+1,k)`. -/
def jacobiFactor (N : ℕ) (z : ℝ) (k : Fin (N - 1)) :
    Matrix (Fin N) (Fin N) ℝ :=
  1 + z • elementaryMatrix (i := ⟨k.val + 1, by omega⟩) (j := ⟨k.val, by omega⟩)

/-- The factors are multiplied in the displayed descending row order. -/
def descendingJacobiProduct (N : ℕ) (z : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  ((List.finRange (N - 1)).reverse.map (jacobiFactor N z)).prod

/--
Jacobi-chip factorization of the finite lower triangular Toeplitz matrix.
The hypothesis `2 ≤ N` is the implicit size condition in the displayed
endpoints `N - 1` and `N - 2`.
-/
def jacobiChipFactorization : Prop :=
  ∀ (N : ℕ) (z : ℝ), 2 ≤ N →
    toeplitzMatrix N z = descendingJacobiProduct N z

end MathlibPlus.Open.LinearAlgebra.FiniteToeplitzMoment
