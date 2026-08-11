import Mathlib

namespace MathlibPlus.Algebra.AffineSemigroup

/-- Claim 7555: the displayed affine maps compose multiplicatively. -/
theorem affineHalf_comp (q₁ q₂ v : ℝ) :
    ((1 - q₁) / 2 + q₁ * ((1 - q₂) / 2 + q₂ * v)) =
      (1 - q₁ * q₂) / 2 + (q₁ * q₂) * v := by
  ring

/-- The map-level form, with the source's parameter range explicit. -/
theorem affineHalf_semigroup {q₁ q₂ : ℝ}
    (_hq₁ : 0 < q₁) (_hq₁' : q₁ < 1)
    (_hq₂ : 0 < q₂) (_hq₂' : q₂ < 1) :
    Function.comp (fun v : ℝ => (1 - q₁) / 2 + q₁ * v)
        (fun v : ℝ => (1 - q₂) / 2 + q₂ * v) =
      (fun v : ℝ => (1 - q₁ * q₂) / 2 + (q₁ * q₂) * v) := by
  funext v
  exact affineHalf_comp q₁ q₂ v

end MathlibPlus.Algebra.AffineSemigroup
