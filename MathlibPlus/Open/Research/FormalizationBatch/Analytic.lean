import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch.Analytic

noncomputable section
open MeasureTheory

/-- The logarithmic-coordinate bare resolvent kernel. -/
def logarithmicResolventKernel (c y z : ℝ) : ℝ :=
  if y ≤ z then c⁻¹ * Real.exp (-(z - y) / c) else 0

/-- Claim 18153: the logarithmic resolvent is forward-supported and has unit
mass in the transition variable. -/
def claim_18153 : Prop :=
  ∀ c : ℝ, 0 < c →
    (∀ y z : ℝ, z < y → logarithmicResolventKernel c y z = 0) ∧
    (∀ y : ℝ, ∫ z : ℝ, logarithmicResolventKernel c y z = 1)

end
end MathlibPlus.Open.Research.FormalizationBatch.Analytic
