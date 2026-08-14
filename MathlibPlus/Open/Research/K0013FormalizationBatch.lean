import Mathlib

namespace MathlibPlus.Open.Research.K0013FormalizationBatch

open scoped BigOperators

noncomputable section

/-- The rising factorial `(α)_n`. -/
def risingFactorial (α : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (α + (k : ℝ))

/-- The moments `h_n = (α)_n / (2n)!` used in the completed Bezout matrix. -/
def gammaMoment (α : ℝ) (n : ℕ) : ℝ :=
  risingFactorial α n / (Nat.factorial (2 * n) : ℝ)

/-- The entries of the completed Bezout matrix. -/
def completedBezoutEntry (α : ℝ) (i j : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (min i j + 1),
    ((i + j + 1 - 2 * a : ℕ) : ℝ) *
      gammaMoment α a * gammaMoment α (i + j + 1 - a)

/-- The leading `N × N` section `C^(N)` of the completed Bezout matrix. -/
def completedBezoutSection (α : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => completedBezoutEntry α i.val j.val

/-- The recursively normalized pivot factors `q_j`. -/
def pivotScale (j : ℕ) : ℝ :=
  2 * ∏ u ∈ Finset.range j,
    (2 : ℝ) * (4 * (u : ℝ) + 1) *
      (4 * (u : ℝ) + 3) ^ 2 * (4 * (u : ℝ) + 5)

/-- The determinant wall product asserted for every rank. -/
def claim7505 : Prop :=
  ∀ (α : ℝ) (N : ℕ),
    let K_N := ∏ j ∈ Finset.range N, (pivotScale j)⁻¹
    Matrix.det (completedBezoutSection α N) =
        K_N *
          (∏ j ∈ Finset.range N, (α + (j : ℝ)) ^ (N - j)) *
          (∏ k ∈ (Finset.range N).erase 0,
            (2 * α - (2 * (k : ℝ) - 1)) ^ (N - k)) ∧
      0 < K_N

end

end MathlibPlus.Open.Research.K0013FormalizationBatch
