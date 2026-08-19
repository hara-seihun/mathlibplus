import MathlibPlus.Analysis.ThetaMellin
import MathlibPlus.Open.Analysis.AdmittedGreenKernelBoundary
import MathlibPlus.Open.Analysis.CompletedThetaFormalizationBatch
import MathlibPlus.Open.Analysis.CompletedThetaToeplitz
import MathlibPlus.Open.Analysis.GreenKernel
import MathlibPlus.Open.FormalizationBatch.TransformDeflation
import MathlibPlus.Open.ProjectsResearch.GammaMixture7462
import MathlibPlus.Open.ResearchFormalization_12527_12532_01a00b46

namespace MathlibPlus.Open.Analysis

open scoped BigOperators

/-- The admitted single-source identification for all completed-theta
presentations, including the positive-index reindexings and Toeplitz shell. -/
def completedThetaSingleSourceClaim61354 : Prop :=
  let φ : ℕ → ℝ → ℝ := fun n u =>
    (4 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) -
        6 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
      Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u))
  let Φ : ℝ → ℝ := fun u =>
    ∑' n : {n : ℕ // 0 < n}, φ n.1 u
  (∀ u : ℝ,
      MathlibPlus.Analysis.ThetaMellin.completedThetaKernel u = Φ u) ∧
    (∀ u : ℝ,
      MathlibPlus.Open.FormalizationBatch.TransformDeflation.completedThetaKernel u =
        Φ u) ∧
    (∀ u : ℝ,
      MathlibPlus.Open.ProjectsResearch.thetaSource u = Φ u) ∧
    (∀ u : ℝ,
      MathlibPlus.Open.ResearchFormalization_12527_12532_01a00b46.completedThetaPhi u =
        Φ u) ∧
    (∀ u : ℝ,
      MathlibPlus.Analysis.GreenKernel.thetaPhiBase u = Φ u) ∧
    (∀ u : ℝ,
      MathlibPlus.Open.Analysis.greenPhiRaw u = Φ u) ∧
    (∀ u : ℝ,
      MathlibPlus.Open.Analysis.CompletedThetaFormalizationBatch.completedThetaKernel u =
        Φ u) ∧
    (∀ u : ℝ,
      MathlibPlus.Open.Analysis.completedThetaSource u = Φ |u|) ∧
    (∀ u : ℝ,
      (∑' n : ℕ, φ (n + 1) u) = Φ u) ∧
    (∀ u : ℝ,
      (∑' n : ℕ, if 0 < n then φ n u else 0) = Φ u) ∧
    (∀ u : ℝ,
      (∑' n : {n : ℕ // 0 < n}, φ n.1 u) = Φ u) ∧
    (∀ u : ℝ,
      (∑' n : ℕ, φ n u) = Φ u) ∧
    (∀ n : ℕ, ∀ u : ℝ,
      MathlibPlus.Open.Analysis.completedThetaShell n u = φ n u) ∧
    (∀ n : ℕ, ∀ u : ℝ,
      let x_n : ℝ := Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u)
      2 * Real.exp (u / 2) * x_n * (2 * x_n - 3) * Real.exp (-x_n) =
        φ n u)

end MathlibPlus.Open.Analysis
