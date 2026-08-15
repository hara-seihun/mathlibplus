import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/-- The principal nonnegative Lambert branch on the nonnegative half-line. -/
noncomputable def principalLambertW (x : ℝ) : ℝ :=
  if 0 ≤ x then sInf {w : ℝ | 0 ≤ w ∧ w * Real.exp w = x} else 0

/-- `W_j = W₀(j/(2π))` from the compact Lambert model. -/
noncomputable def compactLambertW (j : ℕ) : ℝ :=
  principalLambertW ((j : ℝ) / (2 * Real.pi))

/-- `a_j^* = W_j/(4j)`. -/
noncomputable def compactLambertCoefficient (j : ℕ) : ℝ :=
  compactLambertW j / (4 * (j : ℝ))

/-- The starred monic norm product, with base norm `μ₀`. -/
noncomputable def compactLambertNorm (μ₀ : ℝ) (k : ℕ) : ℝ :=
  μ₀ * Finset.prod (Finset.Icc 1 (2 * k))
    (fun j => (compactLambertCoefficient j) ^ 2)

/-- `c_N^* = a_N^*`. -/
noncomputable def compactLambertTerminalCoefficient (N : ℕ) : ℝ :=
  compactLambertCoefficient N

/-- The trailing Lambert sum `S_{m,N}`. -/
noncomputable def compactLambertAction (m N : ℕ) : ℝ :=
  Finset.sum (Finset.Icc (m + 1) N)
    (fun j => compactLambertW N - compactLambertW j)

/-- Consecutive-norm denominator action equals `8`. -/
def consecutiveNormDenominatorActionEqualsEight (μ₀ : ℝ) : Prop :=
  (∀ n : ℕ, 1 ≤ n →
    Real.log ((compactLambertNorm μ₀ n * compactLambertNorm μ₀ (n - 1)) /
      (μ₀ ^ 2 * compactLambertTerminalCoefficient (2 * n) ^ (8 * n - 4))) =
      4 * compactLambertAction 0 (2 * n) -
        2 * (compactLambertW (2 * n) - compactLambertW (2 * n - 1))) ∧
  Filter.Tendsto
    (fun n : ℕ =>
      Real.log ((compactLambertNorm μ₀ n * compactLambertNorm μ₀ (n - 1)) /
        (μ₀ ^ 2 * compactLambertTerminalCoefficient (2 * n) ^ (8 * n - 4))) /
        (n : ℝ))
    Filter.atTop (nhds (8 : ℝ))

end MathlibPlus.Open.Analysis
