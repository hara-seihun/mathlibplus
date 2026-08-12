import Mathlib

namespace MathlibPlus.Algebra.Claim52300

/-- Exact rational arithmetic in the bottom-edge parameter check of claim 52300. -/
theorem exactBottomEdgeParameterIdentity :
    let t₀ : ℚ := 2977 / 20000
    let y₀ : ℚ := 9 / 100
    t₀ + y₀ ^ 2 / 2 = 1529 / 10000 ∧
      y₀ ^ 2 < 1 - 2 * t₀ := by
  norm_num

end MathlibPlus.Algebra.Claim52300
