import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- The endpoint fixed by the leased equilibrium-potential statement. -/
def potentialEndpoint : ℝ := Real.pi / 2

/-- The arcsine-mixture density specified in the repair context. -/
def equilibriumDensity (b z : ℝ) : ℝ :=
  2 * ∫ u in (0 : ℝ)..1,
    if 0 < z ∧ z < b / u then
      1 / (Real.pi * Real.sqrt ((b / u) ^ 2 - z ^ 2))
    else
      0

/-- The explicit potential specified in the repair context. -/
def equilibriumPotential (b s : ℝ) : ℝ :=
  2 * Real.arsinh (Real.sqrt s / b) -
    2 * Real.sqrt s / (Real.sqrt (s + b ^ 2) + b)

/-- Explicit logarithmic potential difference for the equilibrium at `b = π / 2`. -/
def explicitLogarithmicPotentialDifference : Prop :=
  ∀ s s₀ : ℝ, 0 < s → 0 < s₀ →
    (∫ z in Set.Ioi (0 : ℝ),
      Real.log ((s + z ^ 2) / (s₀ + z ^ 2)) * equilibriumDensity potentialEndpoint z) =
      equilibriumPotential potentialEndpoint s - equilibriumPotential potentialEndpoint s₀

end

end MathlibPlus.Open.Analysis
