import Mathlib

namespace MathlibPlus.Analysis.Claim53272

/-- The packet's displayed entropy difference, with its binary-entropy
expression made explicit.  The source's area functional and the two-bit
policy semantics are not reconstructed here because those carriers are not
defined in the admitted claim. -/
theorem exactEntropyDifference_claim53272 :
    let h : ℝ → ℝ := fun p => -p * Real.log p - (1 - p) * Real.log (1 - p)
    h (3 / 4) - (Real.log 2 + h (19 / 24) - h (7 / 12)) =
        (19 * Real.log 19 - 18 * Real.log 3 -
          14 * Real.log 7 - 5 * Real.log 5) / 24 := by
  dsimp
  norm_num
  have h34 : Real.log ((3 : ℝ) / 4) = Real.log 3 - Real.log 4 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
  have h14 : Real.log ((1 : ℝ) / 4) = -Real.log 4 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    simp
  have h1924 : Real.log ((19 : ℝ) / 24) = Real.log 19 - Real.log 24 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
  have h524 : Real.log ((5 : ℝ) / 24) = Real.log 5 - Real.log 24 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
  have h712 : Real.log ((7 : ℝ) / 12) = Real.log 7 - Real.log 12 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
  have h512 : Real.log ((5 : ℝ) / 12) = Real.log 5 - Real.log 12 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
  have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 3 using 1 <;> norm_num
  have h12 : Real.log (12 : ℝ) = Real.log 3 + 2 * Real.log 2 := by
    calc
      Real.log (12 : ℝ) = Real.log ((3 : ℝ) * 4) := by norm_num
      _ = Real.log 3 + Real.log 4 := by rw [Real.log_mul] <;> norm_num
      _ = Real.log 3 + 2 * Real.log 2 := by rw [h4]
  have h24 : Real.log (24 : ℝ) = Real.log 3 + 3 * Real.log 2 := by
    calc
      Real.log (24 : ℝ) = Real.log ((3 : ℝ) * 8) := by norm_num
      _ = Real.log 3 + Real.log 8 := by rw [Real.log_mul] <;> norm_num
      _ = Real.log 3 + 3 * Real.log 2 := by rw [h8]
  rw [h34, h14, h1924, h524, h712, h512, h4, h12, h24]
  ring

/-- The exact strict sign certificate accompanying the entropy difference. -/
theorem logGapPositive_claim53272 :
    (19 : ℕ) ^ 19 > 3 ^ 18 * 7 ^ 14 * 5 ^ 5 ∧
      0 < (19 * Real.log 19 - 18 * Real.log 3 -
        14 * Real.log 7 - 5 * Real.log 5) / 24 := by
  constructor
  · norm_num
  · have hleft : (0 : ℝ) < (3 : ℝ) ^ 18 * 7 ^ 14 * 5 ^ 5 := by
      positivity
    have hright : (3 : ℝ) ^ 18 * 7 ^ 14 * 5 ^ 5 < (19 : ℝ) ^ 19 := by
      norm_num
    have hlog : Real.log ((3 : ℝ) ^ 18 * 7 ^ 14 * 5 ^ 5) <
        Real.log ((19 : ℝ) ^ 19) := by
      exact Real.strictMonoOn_log hleft
        (by
          change (0 : ℝ) < (19 : ℝ) ^ 19
          positivity) hright
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)] at hlog
    simp only [Real.log_pow] at hlog
    have hnum : 0 < 19 * Real.log 19 - 18 * Real.log 3 -
        14 * Real.log 7 - 5 * Real.log 5 := by
      norm_num at hlog
      linarith [hlog]
    exact div_pos hnum (by norm_num)

end MathlibPlus.Analysis.Claim53272
