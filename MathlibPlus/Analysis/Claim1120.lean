import Mathlib

namespace MathlibPlus.Analysis.Claim1120

/-- The Dusart-tail comparison is exactly the displayed cubic inequality from claim 1120,
under the positive-denominator domain used when clearing fractions. -/
theorem dusartComparison_iff_Q_pos_claim1120 (x L c : ℝ)
    (hx : 0 < x) (hL : 0 < L) (hLc : 0 < L - c) :
    x / L * (1 + 1 / L + 2 / L ^ 2 + (759 / 100 : ℝ) / L ^ 3) <
        x / (L - c) ↔
      (c - 1) * L ^ 3 - (2 - c) * L ^ 2 -
          ((759 / 100 : ℝ) - 2 * c) * L + (759 / 100 : ℝ) * c > 0 := by
  have hL0 : L ≠ 0 := ne_of_gt hL
  have hLc0 : L - c ≠ 0 := ne_of_gt hLc
  constructor <;> intro h
  · field_simp [hL0, hLc0] at h
    nlinarith
  · field_simp [hL0, hLc0]
    nlinarith

/-- The displayed Dusart polynomial is strictly increasing in its coefficient
parameter whenever the logarithmic variable is positive. -/
theorem dusartTail_Q_strictMono_claim1120 (L c₁ c₂ : ℝ)
    (hL : 0 < L) (hc : c₁ < c₂) :
    (c₁ - 1) * L ^ 3 - (2 - c₁) * L ^ 2 -
          ((759 / 100 : ℝ) - 2 * c₁) * L + (759 / 100 : ℝ) * c₁ <
      (c₂ - 1) * L ^ 3 - (2 - c₂) * L ^ 2 -
          ((759 / 100 : ℝ) - 2 * c₂) * L + (759 / 100 : ℝ) * c₂ := by
  have hp : 0 < L ^ 3 + L ^ 2 + 2 * L + (759 / 100 : ℝ) := by
    positivity
  nlinarith

end MathlibPlus.Analysis.Claim1120
