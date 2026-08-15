import Mathlib

namespace MathlibPlus.Open.Analysis.Claim8960

noncomputable def saturationEdge (α : ℝ) : ℝ :=
  Real.pi / (2 * α)

noncomputable def fillingEquilibrium (α z : ℝ) : ℝ :=
  if 0 < z ∧ z < saturationEdge α then
    (α * z ^ 2)⁻¹ * (1 - Real.sqrt (1 - (z / saturationEdge α) ^ 2))
  else if saturationEdge α ≤ z then
    (α * z ^ 2)⁻¹
  else
    0

/-- For every positive filling, the saturated tail has particle fraction `2 / π`. -/
noncomputable def fillingIndependentSaturatedFraction_claim8960 : Prop :=
  ∀ α : ℝ, 0 < α →
    ∫ z in Set.Ici (saturationEdge α), fillingEquilibrium α z = 2 / Real.pi

end MathlibPlus.Open.Analysis.Claim8960
