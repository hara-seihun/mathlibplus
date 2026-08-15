import Mathlib

namespace MathlibPlus.Open.Analysis.Claim8966

noncomputable def saturationEdge_claim8956 (α : ℝ) : ℝ :=
  Real.pi / (2 * α)

noncomputable def rho_claim8957 (α z : ℝ) : ℝ :=
  if 0 < z ∧ z < saturationEdge_claim8956 α then
    (α * z ^ 2)⁻¹ * (1 - Real.sqrt (1 - (z / saturationEdge_claim8956 α) ^ 2))
  else if saturationEdge_claim8956 α ≤ z then
    (α * z ^ 2)⁻¹
  else
    0

/-- Explicit logarithmic moment from admitted Claim 8966. -/
def explicitLogarithmicMoment_claim8966 : Prop :=
  ∀ α : ℝ, 0 < α →
    (∫ z in Set.Ioi (0 : ℝ), Real.log z * rho_claim8957 α z) =
      1 + Real.log (Real.pi / (4 * α))

end MathlibPlus.Open.Analysis.Claim8966
