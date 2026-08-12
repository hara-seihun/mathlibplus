import Mathlib.Tactic

namespace MathlibPlus.Algebra

/-!
Two exact arithmetic certificates from the displayed rank-two kernels.  The
source formulas are kept inside the theorem statements so these certificates
refer to the stated kernels rather than to unconstrained replacement
functions.
-/

/-- Claim 17608: the displayed dispersion polynomial is positive on the
nonnegative quadrant. -/
theorem dispersionPositive_claim17608 {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    let R : ℝ → ℝ → ℝ := fun x y =>
      7 * x ^ 2 + 17 * x * y + 7 * y ^ 2 - 600 * (x + y) + 23040
    R x y > 0 := by
  dsimp
  nlinarith [sq_nonneg (7 * (x + y) - 300), mul_nonneg hx hy]

/-- Claim 18382: the displayed polarized rank-two kernel has a negative
boundary face at `(1, 1, 0, 0)`. -/
theorem kFourNegativeFace_claim18382 :
    let K₄ : ℝ → ℝ → ℝ → ℝ → ℝ := fun x₁ x₂ x₃ x₄ =>
      let e₁ := x₁ + x₂ + x₃ + x₄
      let e₂ := x₁ * x₂ + x₁ * x₃ + x₁ * x₄ + x₂ * x₃ + x₂ * x₄ + x₃ * x₄
      let e₃ := x₁ * x₂ * x₃ + x₁ * x₂ * x₄ + x₁ * x₃ * x₄ + x₂ * x₃ * x₄
      let e₄ := x₁ * x₂ * x₃ * x₄
      e₁ ^ 2 * e₂ / 92160 + 13 * e₁ * e₃ / 69120 -
        13 * e₂ ^ 2 / 138240 - 11 * e₄ / 34560
    K₄ 1 1 0 0 = -(7 : ℝ) / 138240 ∧ K₄ 1 1 0 0 < 0 := by
  norm_num

end MathlibPlus.Algebra
