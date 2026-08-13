import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

namespace MathlibPlus.Open.Analysis

/-- Claim 6961: the shifted-gamma kernel has the stated positive mass, and
normalizing by that mass gives a probability density. -/
def massAndProbabilityDensity_claim6961 : Prop :=
  ∀ (μ σ : ℝ), 0 < μ + σ / 2 →
    let g : ℝ → ℝ := fun u =>
      (2 : ℝ) * Real.pi ^ μ *
        Real.exp ((2 * μ + σ) * u - Real.pi * Real.exp (2 * u))
    let C : ℝ := Real.pi ^ (-σ / 2) * Real.Gamma (μ + σ / 2)
    Integrable g ∧
      (∀ u, 0 ≤ g u) ∧
      (∫ u, g u) = C ∧
      0 < C ∧
      Integrable (fun u => g u / C) ∧
      (∀ u, 0 ≤ g u / C) ∧
      (∫ u, g u / C) = 1

end MathlibPlus.Open.Analysis
