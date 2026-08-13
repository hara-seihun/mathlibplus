import Mathlib

namespace MathlibPlus.Analysis.Claim12443

/--
Claim 12443.  The arithmetic sample is the displayed quantity
`z = n * exp x / c`; the support conclusion is stated with its strict
absolute-value interval exactly as in the claim.  The upper constraints are
retained, although the lower bound itself needs only `c > 1`, `x ≥ 0`, and
`n ≥ 1`.
-/
theorem firstSampleSupportGap
    (c x n : ℝ) (hc : 1 < c) (hx : 0 ≤ x) (_hxc : x ≤ Real.log c)
    (hn1 : 1 ≤ n) (_hn : n ≤ c * Real.exp (-x)) :
    let z : ℝ := n * Real.exp x / c
    z ≥ 1 / c ∧ ¬ (0 < |z| ∧ |z| < 1 / c) := by
  let z : ℝ := n * Real.exp x / c
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hexp : 1 ≤ Real.exp x := Real.one_le_exp hx
  have hprod : 1 ≤ n * Real.exp x := by
    calc
      (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ n * 1 := by gcongr
      _ ≤ n * Real.exp x := by gcongr
  have hbound : (1 : ℝ) / c ≤ n * Real.exp x / c := by
    exact (div_le_div_iff_of_pos_right hc0).mpr hprod
  have hz : 0 ≤ z := by
    dsimp [z]
    positivity
  have hzbound : 1 / c ≤ z := by
    exact hbound
  refine ⟨hzbound, ?_⟩
  intro h
  have hzlt : z < 1 / c := by
    rw [abs_of_nonneg hz] at h
    exact h.2
  exact (not_lt_of_ge hzbound) hzlt

end MathlibPlus.Analysis.Claim12443
