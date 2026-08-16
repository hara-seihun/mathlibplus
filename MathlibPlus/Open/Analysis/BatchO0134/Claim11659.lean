import Mathlib

noncomputable section
open scoped BigOperators
open Filter

namespace MathlibPlus.Open.Analysis.BatchO0134.Claim11659

private def productFactors (m : ℕ) (τ : ℝ) : ℝ :=
  ∏ j ∈ Finset.Icc (1 : ℕ) m, (j : ℝ) ^ 2 + τ ^ 2 / 4

private def normalizedMultiplier (m : ℕ) (τ : ℝ) : ℝ :=
  Real.exp (2 * (m : ℝ)) /
      (8 * (m : ℝ) ^ (2 * m + 2) * Real.cosh (Real.pi * τ / 2)) *
    productFactors m τ

private def fixedFrequencyLimit (τ : ℝ) : ℝ :=
  if τ = 0 then Real.pi / 4 else Real.tanh (Real.pi * τ / 2) / (2 * τ)

def fixedFrequencyAsymptotic : Prop :=
  ∀ (τ : ℝ),
    Tendsto (fun m : ℕ => (m : ℝ) * normalizedMultiplier m τ) atTop
      (nhds (fixedFrequencyLimit τ))

end MathlibPlus.Open.Analysis.BatchO0134.Claim11659
