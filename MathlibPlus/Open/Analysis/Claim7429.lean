import Mathlib

namespace MathlibPlus.Open.Analysis.Claim7429

def logisticSpectralMean_claim7429 : Prop :=
  ∀ (a q t : ℝ),
    let K : ℝ → ℝ → ℝ := fun q t =>
      Real.exp (-a * t - q * Real.exp (-t)) +
        Real.exp (a * t - q * Real.exp t)
    let p : ℝ := -(deriv (fun q' : ℝ => K q' t) q) / K q t
    p = Real.cosh t + Real.sinh t * Real.tanh (a * t - q * Real.sinh t) ∧
      Real.exp (-t) < p ∧ p < Real.exp t

end MathlibPlus.Open.Analysis.Claim7429
