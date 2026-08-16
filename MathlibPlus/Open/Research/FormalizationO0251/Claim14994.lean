import Mathlib

namespace MathlibPlus.Open.Research.FormalizationO0251

/-- The Dini factor displayed in the shifted-Euler shadow-plus-Dini model. -/
noncomputable def diniFactor (L z : ℝ) : ℝ :=
  (z * Real.sin (L * z) - (1 / 2 : ℝ) * Real.cos (L * z)) /
    (z ^ 2 + 1 / 4)

/-- Claim 14994: the exact Dini value at every integer half-period guard. -/
def exactDiniValueAtHalfPeriod : Prop :=
  ∀ (L : ℝ), 0 < L →
    ∀ (m : ℤ),
      let b_m : ℝ := ((m : ℝ) + 1 / 2) * Real.pi / L
      diniFactor L b_m =
        (-1 : ℝ) ^ m * (b_m / (b_m ^ 2 + 1 / 4))

end MathlibPlus.Open.Research.FormalizationO0251
