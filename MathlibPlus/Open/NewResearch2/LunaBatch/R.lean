import Mathlib

open scoped BigOperators
open Filter

namespace MathlibPlus.Open.NewResearch2.LunaBatch.R

/-- Claim 18432: a moving positivity horizon transfers strict positivity to
any fixed finite rank when the approximation error is below its margin. -/
def claim_18432_abstractEscapingDefectTheorem
    (K : ∀ N : ℕ, Matrix (Fin N) (Fin N) ℝ)
    (Kapprox : ∀ N M : ℕ, Matrix (Fin N) (Fin N) ℝ)
    (H : ℕ → ℕ) (epsilon : ℕ → ℕ → ℝ) : Prop :=
  let vecNorm : ∀ N : ℕ, (Fin N → ℝ) → ℝ := fun N x =>
    Real.sqrt (∑ i : Fin N, x i ^ 2)
  let operatorError : ∀ N M : ℕ, ℝ := fun N M =>
    sSup {z : ℝ | ∃ x : Fin N → ℝ,
      vecNorm N x ≤ 1 ∧
        z = vecNorm N ((K N - Kapprox N M).mulVec x)}
  Tendsto H atTop atTop ∧
    (∀ N M : ℕ, N < H M →
      0 < epsilon N M ∧
      (∀ x : Fin N → ℝ,
        epsilon N M * (∑ i : Fin N, x i ^ 2) ≤
          ∑ i : Fin N, ∑ j : Fin N,
            x i * Kapprox N M i j * x j) ∧
      operatorError N M < epsilon N M) →
    (∀ N : ℕ, ∀ x : Fin N → ℝ, x ≠ 0 →
      0 < ∑ i : Fin N, ∑ j : Fin N, x i * K N i j * x j)

end MathlibPlus.Open.NewResearch2.LunaBatch.R
