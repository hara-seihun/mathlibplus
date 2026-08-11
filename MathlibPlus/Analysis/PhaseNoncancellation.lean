import Mathlib

namespace MathlibPlus.Analysis.PhaseNoncancellation

/-- Adjacent cosine phases cannot both vanish when the phase separation is not a
multiple of a half-turn.  This is the displayed inequality behind the
adjacent-order cancellation obstruction in claim 9247. -/
theorem adjacentPhaseNoncancellation :
    ∀ φ θ : ℝ, |Real.cos θ| < 1 →
      1 - |Real.cos θ| ≤ Real.cos φ ^ 2 + Real.cos (φ + θ) ^ 2 ∧
        0 < 1 - |Real.cos θ| := by
  intro φ θ hθ
  have hident :
      Real.cos φ ^ 2 + Real.cos (φ + θ) ^ 2 =
        1 + Real.cos θ * Real.cos (2 * φ + θ) := by
    rw [Real.cos_add, Real.cos_add, Real.cos_two_mul, Real.sin_two_mul]
    nlinarith [Real.cos_sq_add_sin_sq φ, Real.cos_sq_add_sin_sq θ]
  have hz : |Real.cos (2 * φ + θ)| ≤ 1 := by
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hprod : |Real.cos θ * Real.cos (2 * φ + θ)| ≤ |Real.cos θ| := by
    rw [abs_mul]
    calc
      |Real.cos θ| * |Real.cos (2 * φ + θ)| ≤ |Real.cos θ| * 1 :=
        mul_le_mul_of_nonneg_left hz (abs_nonneg _)
      _ = |Real.cos θ| := by ring
  have hlower : -|Real.cos θ| ≤ Real.cos θ * Real.cos (2 * φ + θ) := by
    calc
      -|Real.cos θ| ≤ -|Real.cos θ * Real.cos (2 * φ + θ)| := by linarith
      _ ≤ Real.cos θ * Real.cos (2 * φ + θ) := neg_abs_le _
  constructor
  · nlinarith [hident]
  · exact sub_pos.mpr hθ

end MathlibPlus.Analysis.PhaseNoncancellation
