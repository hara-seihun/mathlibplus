import Mathlib

namespace MathlibPlus.Open.Analysis

def sharp_boundary_accessibility_1915 : Prop :=
  let R : ℝ := 4.81
  let H : ℝ := 3 * (10 : ℝ) ^ 12
  let K : ℝ := 16
  let T₀ : ℝ := (10 : ℝ) ^ 10
  let σ₀ : ℝ := 1 - (1 / R) / Real.log (K * H + T₀)
  let d₀ : ℝ := 2 * σ₀ - 1
  let cstar : ℝ := 46110325513857 / 46729244180480
  d₀ - cstar > 4.5787500636674310 * (10 : ℝ) ^ (-5 : ℤ)

end MathlibPlus.Open.Analysis
