import Mathlib

namespace MathlibPlus.Algebra.Claim18481

/-- The rotated residual factor from the source identity. -/
def rotatedResidual (ρ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 + 4 * x) * ρ x

theorem rotatedResidual_eq (ρ : ℝ → ℝ) (x : ℝ) :
    rotatedResidual ρ x = (1 + 4 * x) * ρ x := by
  rfl

end MathlibPlus.Algebra.Claim18481
