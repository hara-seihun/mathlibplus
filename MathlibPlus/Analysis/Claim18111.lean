import Mathlib

namespace MathlibPlus.Analysis

/-- Admitted claim 18111: `x ↦ 1 - x⁻²` is strictly increasing on the
positive real axis. -/
theorem momentCurveCoordinate_strictMono :
    StrictMonoOn (fun x : ℝ => 1 - x⁻¹ ^ 2) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have h_inv : y⁻¹ < x⁻¹ := (inv_lt_inv₀ hy hx).2 hxy
  have hsq : y⁻¹ ^ 2 < x⁻¹ ^ 2 :=
    (sq_lt_sq₀ (le_of_lt (inv_pos.mpr hy)) (le_of_lt (inv_pos.mpr hx))).2 h_inv
  linarith

end MathlibPlus.Analysis
