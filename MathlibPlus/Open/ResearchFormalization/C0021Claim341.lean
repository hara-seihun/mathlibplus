import MathlibPlus.Analysis.ThetaMellin

namespace MathlibPlus.Open.ResearchFormalization.C0021Claim341

open MathlibPlus.Analysis.ThetaMellin

noncomputable section

/-- The completed-theta positive-index shell formula and its source-indexed
infinite sum, anchored to the canonical completed theta kernel. -/
def claim341 : Prop :=
  ∀ (u : ℝ), 0 ≤ u →
    (completedThetaKernel u =
      ∑' n : {n : ℕ // 1 ≤ n}, thetaShell n.1 u) ∧
    (∀ (n : ℕ), 1 ≤ n →
      0 < thetaShell n u ∧
        thetaShell n u =
          (4 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) -
            6 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
              Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u)) ∧
        thetaShell n u =
          2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u / 2) *
            (2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u) - 3) *
              Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u)))

end

end MathlibPlus.Open.ResearchFormalization.C0021Claim341
