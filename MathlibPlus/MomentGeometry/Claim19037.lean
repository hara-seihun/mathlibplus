import Mathlib

namespace MathlibPlus.MomentGeometry.TwoAtomJensen

/-- Every finite moment Hankel matrix for `δ₁ + (1/10)δ₄` is positive
semidefinite. -/
def moment_hankel_posSemidef : Prop :=
  ∀ m : ℕ,
    Matrix.PosSemidef (fun i j : Fin m =>
      (1 : ℝ) + (1 / 10 : ℝ) * 4 ^ ((i : ℕ) + (j : ℕ)))

/-- The displayed quadratic Jensen section has the exact negative
 discriminant and no real roots. -/
def quadratic_jensen_section : Prop :=
  let a₀ : ℝ := 11 / 10
  let a₁ : ℝ := 13 / 10
  let a₂ : ℝ := 133 / 60
  (4 * (a₁ ^ 2 - a₀ * a₂) = -(449 : ℝ) / 150) ∧
    ∀ x : ℝ, a₀ + 2 * a₁ * x + a₂ * x ^ 2 ≠ 0

end MathlibPlus.MomentGeometry.TwoAtomJensen
