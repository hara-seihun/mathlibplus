import Mathlib

/-!
# Classical zero-free boundary arithmetic

This file formalizes the exact denominator comparison in Record 3 of legacy packet
`C-0105`. It compares the geometric boundaries only and does not assert that the
Riemann zeta function is zero-free in any of the regions.
-/

namespace MathlibPlus.ZeroFreeBoundary

/-- The denominator `4.852` is strictly smaller than `4.8568` and `4.862`, so for
every `t ≥ 2` its classical logarithmic boundary lies strictly farther left. -/
theorem denominator4852_strictImprovement :
    ((6071 : ℝ) / 1250 - 1213 / 250 = 3 / 625) ∧
    ((2431 : ℝ) / 500 - 1213 / 250 = 1 / 100) ∧
    ∀ t : ℝ, 2 ≤ t →
      1 - 1 / (((1213 : ℝ) / 250) * Real.log t) <
          1 - 1 / (((6071 : ℝ) / 1250) * Real.log t) ∧
      1 - 1 / (((1213 : ℝ) / 250) * Real.log t) <
          1 - 1 / (((2431 : ℝ) / 500) * Real.log t) := by
  constructor
  · norm_num
  constructor
  · norm_num
  intro t ht
  have hlog : 0 < Real.log t := Real.log_pos (lt_of_lt_of_le (by norm_num) ht)
  have boundary_lt {a b : ℝ} (ha : 0 < a) (hab : a < b) :
      1 - 1 / (a * Real.log t) < 1 - 1 / (b * Real.log t) := by
    have hden : 0 < a * Real.log t := mul_pos ha hlog
    have hden_lt : a * Real.log t < b * Real.log t :=
      mul_lt_mul_of_pos_right hab hlog
    have hinv := one_div_lt_one_div_of_lt hden hden_lt
    linarith
  exact ⟨boundary_lt (by norm_num) (by norm_num),
    boundary_lt (by norm_num) (by norm_num)⟩

end MathlibPlus.ZeroFreeBoundary
