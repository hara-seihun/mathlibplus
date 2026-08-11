import Mathlib

/-!
# Elementary exponential bounds

An explicit Taylor bound at `1` gives the rational inequalities and the
negative-exponential consequence recorded in admitted claim 14053.
-/

namespace MathlibPlus.Analysis.ElementaryExponentialBounds

/-- The displayed elementary comparison with `e = Real.exp 1`. -/
theorem elementaryComparison :
    Real.exp 1 < (49 : ℝ) / 18 ∧
    (49 : ℝ) / 18 < 11 / 4 ∧
    (Real.exp 1) ^ 4 < (11 / 4 : ℝ) ^ 4 ∧
    (11 / 4 : ℝ) ^ 4 < 66 ∧
    Real.exp (-2) / 6 - 11 * Real.exp (-6) < 0 := by
  have hbound := Real.exp_bound' (x := (1 : ℝ)) (by norm_num) (by norm_num)
    (n := 4) (by norm_num)
  have he : Real.exp 1 < (49 : ℝ) / 18 := by
    norm_num [Finset.sum_range_succ] at hbound ⊢
    exact lt_of_le_of_lt hbound (by norm_num)
  have heupper : Real.exp 1 < (11 : ℝ) / 4 :=
    lt_trans he (by norm_num)
  have hefour : (Real.exp 1) ^ 4 < (11 / 4 : ℝ) ^ 4 := by
    exact pow_lt_pow_left₀ heupper (by positivity) (by norm_num)
  have hfour : (11 / 4 : ℝ) ^ 4 < 66 := by norm_num
  have hexpfour : Real.exp 4 < 66 := by
    calc
      Real.exp 4 = (Real.exp 1) ^ 4 := by
        convert Real.exp_nat_mul (1 : ℝ) 4 using 1; norm_num
      _ < 66 := hefour.trans hfour
  have hneg : Real.exp (-2) / 6 - 11 * Real.exp (-6) < 0 := by
    have hfactor : Real.exp (-2) / 6 - 11 * Real.exp (-6) =
        Real.exp (-6) * (Real.exp 4 / 6 - 11) := by
      rw [show (-2 : ℝ) = -6 + 4 by norm_num, Real.exp_add]
      ring
    rw [hfactor]
    have hbracket : Real.exp 4 / 6 - 11 < 0 := by nlinarith
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) hbracket
  exact ⟨he, by norm_num, hefour, hfour, hneg⟩

end MathlibPlus.Analysis.ElementaryExponentialBounds
