import Mathlib

namespace MathlibPlus.Open.Analysis.Claim8963

noncomputable section

/-- The saturation edge at filling `α`. -/
def saturationEdge_claim8963 (α : ℝ) : ℝ :=
  Real.pi / (2 * α)

/-- The constrained equilibrium density on the positive integration domain. -/
def equilibriumDensity_claim8963 (α z : ℝ) : ℝ :=
  if 0 < z then
    if z < saturationEdge_claim8963 α then
      (α * z ^ 2)⁻¹ *
        (1 - Real.sqrt (1 - (z / saturationEdge_claim8963 α) ^ 2))
    else
      (α * z ^ 2)⁻¹
  else
    0

/-- Explicit negative-axis transform at filling `α`. -/
def explicitNegativeAxisTransform_claim8963 : Prop :=
  ∀ (α s : ℝ),
    0 < α →
    0 < s →
      (∫ z in Set.Ioi (0 : ℝ),
          equilibriumDensity_claim8963 α z / (s + z ^ 2)) =
        1 / (Real.sqrt s *
          (Real.sqrt (s + saturationEdge_claim8963 α ^ 2) +
            saturationEdge_claim8963 α))

end

end MathlibPlus.Open.Analysis.Claim8963
