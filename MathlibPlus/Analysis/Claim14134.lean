import Mathlib

namespace MathlibPlus.Analysis.Claim14134

/-- Dyadic square energy for a complex coefficient sequence, with the finite
range `N ≤ k < 2N` written as `Finset.Ico N (2 * N)`. -/
noncomputable def dyadicSquareEnergy (c : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico N (2 * N),
    Real.sqrt (k : ℝ) * ‖c k‖ ^ 2

/-- The dyadic square energy is nonnegative. -/
theorem dyadicSquareEnergy_nonneg (c : ℕ → ℂ) (N : ℕ) :
    0 ≤ dyadicSquareEnergy c N := by
  unfold dyadicSquareEnergy
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)

end MathlibPlus.Analysis.Claim14134
