import Mathlib

namespace MathlibPlus.AnalyticNumberTheory.Claim3396

/-- The denominator improvement in claim 3396 is exact, and it gives a strict
inclusion of the corresponding half-plane regions at every height `t ≥ 2`. -/
theorem denominatorImprovement
    : let c_old : ℝ := 4.80
      let c_new : ℝ := 4.7975
      c_old - c_new = 1 / 400 ∧ 0 < c_old - c_new ∧
        ∀ t : ℝ, 2 ≤ t →
          Set.Ioi (1 - 1 / (c_old * Real.log t)) ⊂
            Set.Ioi (1 - 1 / (c_new * Real.log t)) := by
  dsimp
  constructor
  · norm_num
  constructor
  · norm_num
  · intro t ht
    have htpos : 0 < t := by linarith
    have hlog : 0 < Real.log t := Real.log_pos (by linarith)
    have hcnew : (0 : ℝ) < 4.7975 := by norm_num
    have hcold : (0 : ℝ) < 4.80 := by norm_num
    have hden_new : 0 < (4.7975 : ℝ) * Real.log t :=
      mul_pos hcnew hlog
    have hden_old : 0 < (4.80 : ℝ) * Real.log t :=
      mul_pos hcold hlog
    have hcoeff : (4.7975 : ℝ) < 4.80 := by norm_num
    have hden : (4.7975 : ℝ) * Real.log t < 4.80 * Real.log t :=
      mul_lt_mul_of_pos_right hcoeff hlog
    have hinv : 1 / (4.80 * Real.log t) <
        1 / ((4.7975 : ℝ) * Real.log t) :=
      one_div_lt_one_div_of_lt hden_new hden
    have hbound :
        1 - 1 / ((4.7975 : ℝ) * Real.log t) <
          1 - 1 / (4.80 * Real.log t) := by linarith
    exact Set.Ioi_ssubset_Ioi hbound

end MathlibPlus.AnalyticNumberTheory.Claim3396
