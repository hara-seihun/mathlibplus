import MathlibPlus.Open.Basic

/-!
# Strict positivity of the completed-theta shells

Statement-fidelity registry node for admitted claim 342 from source record `C-0021`.
The shell is inlined using the factorized formula in the preceding admitted claim
341.  The total kernel is the sum over positive shell labels, reindexed by `n + 1`.
-/

namespace MathlibPlus.Open.Analysis.ThetaShell

/-- Every completed Riemann theta shell is strictly positive on the nonnegative
half-line, the displayed lower bound for its middle factor holds, and their full
sum is strictly positive there. -/
def strictPositivity : Prop :=
  (∀ (u : ℝ) (n : ℕ), 0 ≤ u → 1 ≤ n →
    0 < 2 * Real.pi - 3 ∧
    2 * Real.pi - 3 ≤
      2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u) - 3 ∧
    0 < 2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u / 2) *
      (2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u) - 3) *
      Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u))) ∧
  ∀ u : ℝ, 0 ≤ u →
    0 < ∑' n : ℕ,
      2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (5 * u / 2) *
        (2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) - 3) *
        Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))

end MathlibPlus.Open.Analysis.ThetaShell
