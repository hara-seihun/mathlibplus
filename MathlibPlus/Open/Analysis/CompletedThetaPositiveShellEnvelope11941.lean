import MathlibPlus.Open.Analysis.CompletedThetaToeplitz

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/-- Claim 11941: the completed-theta source has positive shells on the
nonnegative half-line, with the displayed per-shell exponential envelope. -/
noncomputable def completedThetaPositiveShellEnvelope11941 : Prop :=
  let envelope : ℕ → ℝ → ℝ := fun n u =>
    4 * Real.pi ^ 2 * (n : ℝ) ^ 4 *
      Real.exp (9 * u / 2 -
        Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u))
  (∀ (u : ℝ), 0 ≤ u →
      completedThetaSource u =
        ∑' k : ℕ, completedThetaShell (k + 1) u) ∧
    (∀ (n : ℕ) (u : ℝ), 1 ≤ n → 0 ≤ u →
      0 < completedThetaShell n u ∧
      completedThetaShell n u ≤ envelope n u) ∧
    (∀ (n : ℕ), 1 ≤ n →
      AntitoneOn (envelope n) (Set.Ici 0))

end MathlibPlus.Open.Analysis
