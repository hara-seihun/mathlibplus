import Mathlib

namespace MathlibPlus.Open.Research.K0013

open scoped BigOperators

noncomputable section

private def risingFactorial (α : ℝ) (n : ℕ) : ℝ :=
  ∏ u ∈ Finset.range n, (α + (u : ℝ))

private def completedBezoutEntry (α : ℝ) (i j : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (min i j + 1),
    ((i + j + 1 - 2 * a : ℕ) : ℝ) *
      (risingFactorial α a / (Nat.factorial (2 * a) : ℝ)) *
      (risingFactorial α (i + j + 1 - a) /
        (Nat.factorial (2 * (i + j + 1 - a)) : ℝ))

private def completedBezoutSection (α : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => completedBezoutEntry α i.val j.val

private def completedBezoutDeterminant (α : ℝ) (N : ℕ) : ℝ :=
  Matrix.det (completedBezoutSection α N)

private def q (j : ℕ) : ℝ :=
  2 * ∏ v ∈ Finset.range j,
    (2 * (4 * (v : ℝ) + 1) * (4 * (v : ℝ) + 3) ^ 2 * (4 * (v : ℝ) + 5))

private def rankWall (α : ℝ) (k : ℕ) : ℝ :=
  2 * α - (2 * (k : ℝ) - 1)

private def newRankWall (α : ℝ) (N : ℕ) : ℝ :=
  2 * α - (2 * (N : ℝ) - 3)

private def determinantWallFactorization (α : ℝ) (N : ℕ) : Prop :=
  completedBezoutDeterminant α N =
    (∏ j ∈ Finset.range N, (q j)⁻¹) *
      (∏ j ∈ Finset.range N, (α + (j : ℝ)) ^ (N - j)) *
      (∏ k ∈ Finset.range (N - 1),
        rankWall α (k + 1) ^ (N - (k + 1)))

/-- After positivity through rank `N - 1`, the new rank-N sign is the
simple wall factor; the factorization records the inherited multiplicities
of all preceding walls. -/
def claim7507 (α : ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → α > 0 →
    determinantWallFactorization α N ∧
      ((∀ n : ℕ, 1 ≤ n → n < N →
          0 < completedBezoutDeterminant α n) →
        (0 < completedBezoutDeterminant α N ↔ 0 < newRankWall α N))

end
end MathlibPlus.Open.Research.K0013
