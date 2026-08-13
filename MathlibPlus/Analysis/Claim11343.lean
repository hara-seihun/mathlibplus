import Mathlib

namespace MathlibPlus.Analysis.Claim11343

/-- The explicit rational gap in claim 11343 is positive throughout the
high-height range `T ≥ 200`; the source quantities `R`, `E`, and `κ₆` remain
outside this arithmetic extraction. -/
theorem explicitGapPos_claim11343 (T : ℝ) (hT : 200 ≤ T) :
    0 < 4 * (432 * T ^ 4 - 1150 * T ^ 2 - 1875) /
      (T ^ 2 * (16 * T ^ 2 + 25) ^ 2) := by
  have hTpos : 0 < T := by linarith
  have hT2 : 40000 ≤ T ^ 2 := by
    have hprod : 0 ≤ (T - 200) * (T + 200) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hnum : 0 < 4 * (432 * T ^ 4 - 1150 * T ^ 2 - 1875) := by
    have hprod : 0 ≤ (T ^ 2 - 40000) * (T ^ 2 + 40000) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith
  have hden : 0 < T ^ 2 * (16 * T ^ 2 + 25) ^ 2 := by positivity
  exact div_pos hnum hden

/-- If the source quantity `E(1/2,2T/5)` has the displayed exact
rational-gap identity, the claimed strict inequality follows. -/
theorem explicitGapTransfer_claim11343
    (E : ℝ → ℝ → ℝ) (T : ℝ) (hT : 200 ≤ T)
    (hE : E (1 / 2) (2 * T / 5) - 12 / T ^ 2 =
      4 * (432 * T ^ 4 - 1150 * T ^ 2 - 1875) /
        (T ^ 2 * (16 * T ^ 2 + 25) ^ 2)) :
    0 < E (1 / 2) (2 * T / 5) - 12 / T ^ 2 := by
  rw [hE]
  exact explicitGapPos_claim11343 T hT

/-- The companion term `12/T²` is positive in the same range. -/
theorem reciprocalSquarePos_claim11343 (T : ℝ) (hT : 200 ≤ T) :
    0 < 12 / T ^ 2 := by
  have hTpos : 0 < T := by linarith
  positivity

end MathlibPlus.Analysis.Claim11343
