import Mathlib

noncomputable section
open MeasureTheory
open Set

namespace MathlibPlus.Open.FormalizationBatch.K0129

private def saturationEdge (α : ℝ) : ℝ := Real.pi / (2 * α)

private def rhoAlpha (α z : ℝ) : ℝ :=
  if 0 < z ∧ z < saturationEdge α then
    (α * z ^ 2)⁻¹ * (1 - Real.sqrt (1 - (z / saturationEdge α) ^ 2))
  else if saturationEdge α ≤ z then
    (α * z ^ 2)⁻¹
  else
    0

/-- Claim 8959: the filling equilibrium has unit mass. -/
def claim8959 : Prop :=
  ∀ α : ℝ, 0 < α →
    (∫ z in Set.Ioi (0 : ℝ), rhoAlpha α z ∂volume) = 1

end MathlibPlus.Open.FormalizationBatch.K0129
