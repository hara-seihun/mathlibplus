import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim14265

/-- The absolute bilateral exponential moment of the factorial atomic masses
from admitted claim 14265, written as the explicit nonnegative atom series. -/
theorem bilateralExponentialMomentSeries (t : ℝ) :
    (∑' m : ℕ,
      if m = 0 then 0 else
        ((2 * Real.pi) ^ (2 * m) * Real.exp ((2 * (m : ℝ)) * t)) /
          (2 * ((2 * m).factorial : ℝ))) =
      (Real.cosh (2 * Real.pi * Real.exp t) - 1) / 2 := by
  let x : ℝ := 2 * Real.pi * Real.exp t
  have hcosh := Real.hasSum_cosh x
  have htail := hasSum_ite_sub_hasSum hcosh 0
  have hhalf := htail.const_smul (1 / 2 : ℝ)
  have hhalf' :
      HasSum
        (fun m : ℕ =>
          if m = 0 then 0 else
            (1 / 2 : ℝ) * (x ^ (2 * m) / ((2 * m).factorial : ℝ)))
        ((Real.cosh x - 1) / 2) := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hhalf
  rw [← hhalf'.tsum_eq]
  apply tsum_congr
  intro m
  by_cases hm : m = 0
  · simp [hm]
  · simp only [hm, if_false]
    dsimp [x]
    have hexp :
        Real.exp ((2 * (m : ℝ)) * t) = Real.exp t ^ (2 * m) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using Real.exp_nat_mul t (2 * m)
    rw [hexp, mul_pow]
    ring

end MathlibPlus.Analysis.Claim14265
