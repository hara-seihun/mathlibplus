import Mathlib

namespace MathlibPlus.Analysis

/-- Claim 44285, exact scalar envelope. -/
theorem linearExponentialEnvelope_claim44285 (z : ℝ) (hzlo : -1 < z)
    (hzhi : z < 1) :
    1 + z ≤ Real.exp z ∧ Real.exp z ≤ 1 / (1 - z) := by
  constructor
  · simpa [add_comm] using Real.add_one_le_exp z
  · have hpos : 0 < 1 - z := by linarith
    have haux : 1 - z ≤ Real.exp (-z) := by
      nlinarith [Real.add_one_le_exp (-z)]
    have hinv : 1 / Real.exp (-z) ≤ 1 / (1 - z) :=
      one_div_le_one_div_of_le hpos haux
    simpa [one_div, Real.exp_neg] using hinv

/-- Explicit outward-rounded form of the endpoint propagation consequence in
Claim 44285.  `zlo` and `zhi` are the lower and upper enclosure endpoints. -/
theorem linearExponentialEnvelope_rounding_claim44285
    (E0 zlo z zhi : ℝ) (hE0 : 0 < E0)
    (hzlo : -1 < zlo) (hzhi : zhi < 1)
    (hz : zlo ≤ z) (hz' : z ≤ zhi) :
    E0 * (1 + zlo) ≤ E0 * Real.exp z ∧
      E0 * Real.exp z ≤ E0 / (1 - zhi) := by
  have hlo : 1 + zlo ≤ Real.exp z := by
    exact (linearExponentialEnvelope_claim44285 zlo hzlo
      (lt_of_le_of_lt hz (lt_of_le_of_lt hz' hzhi))).1.trans
      (Real.exp_le_exp.mpr hz)
  have hupper : Real.exp z ≤ 1 / (1 - zhi) := by
    have hbase := (linearExponentialEnvelope_claim44285 z
      (lt_of_lt_of_le hzlo hz) (lt_of_le_of_lt hz' hzhi)).2
    have hden : 1 - zhi ≤ 1 - z := by linarith
    have hrec : 1 / (1 - z) ≤ 1 / (1 - zhi) := by
      exact one_div_le_one_div_of_le (by linarith) hden
    exact hbase.trans hrec
  constructor
  · exact mul_le_mul_of_nonneg_left hlo (le_of_lt hE0)
  · have := mul_le_mul_of_nonneg_left hupper (le_of_lt hE0)
    simpa [div_eq_mul_inv] using this

end MathlibPlus.Analysis
