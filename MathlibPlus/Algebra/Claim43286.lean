import Mathlib

namespace MathlibPlus.Algebra.Claim43286

/-- The displayed fourth-order fold, with its explicit source relation. -/
theorem fourthCoefficientFold_algebra_claim43286
    (V A₂ D₃ : ℚ)
    (h : V * D₃ = A₂ ^ 2 + V ^ 4 / 12) :
    let Q := A₂ + V ^ 2 / 2
    V * D₃ + A₂ ^ 2 / 2 + V ^ 2 * A₂ / 2 + V ^ 4 / 24 =
      (6 * Q ^ 2 - 4 * Q * V ^ 2 + V ^ 4) / 4 := by
  dsimp
  rw [h]
  ring

/-- The cubic interpolation coordinate retains the fourth-order fold. -/
def interpolatedCubicCoefficient_claim43286
    (V A₁ A₂ D₂ E₃ σ : ℚ) : ℚ :=
  E₃ + V * D₂ + A₁ * (A₂ + V ^ 2 / 2) +
    σ * (6 * (A₂ + V ^ 2 / 2) ^ 2 -
      4 * (A₂ + V ^ 2 / 2) * V ^ 2 + V ^ 4) / 4

end MathlibPlus.Algebra.Claim43286
