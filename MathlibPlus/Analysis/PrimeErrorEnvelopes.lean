import Mathlib

namespace MathlibPlus.Analysis

/-- The exact coefficient decrease from `121.0961` to `121.096` makes the
common positive FKS envelope strictly smaller at every `x ≥ 2`. -/
theorem thetaEnvelopeAmplitudeImprovement :
    (1210961 : ℝ) / 10000 - 121096 / 1000 = 1 / 10000 ∧
      ∀ x : ℝ, 2 ≤ x →
        (121096 / 1000) *
            Real.rpow (Real.log x / (55666305 / 10000000 : ℝ)) (3 / 2 : ℝ) *
            Real.exp (-2 * Real.sqrt (Real.log x / (55666305 / 10000000 : ℝ))) <
          (1210961 / 10000) *
            Real.rpow (Real.log x / (55666305 / 10000000 : ℝ)) (3 / 2 : ℝ) *
            Real.exp (-2 * Real.sqrt (Real.log x / (55666305 / 10000000 : ℝ))) := by
  constructor
  · norm_num
  · intro x hx
    have hx1 : 1 < x := lt_of_lt_of_le (by norm_num) hx
    have hlog : 0 < Real.log x := Real.log_pos hx1
    have hbase : 0 < Real.log x / (55666305 / 10000000 : ℝ) := by positivity
    have hrpow : 0 < Real.rpow (Real.log x / (55666305 / 10000000 : ℝ)) (3 / 2 : ℝ) :=
      Real.rpow_pos_of_pos hbase _
    have hexp :
        0 < Real.exp (-2 * Real.sqrt (Real.log x / (55666305 / 10000000 : ℝ))) :=
      Real.exp_pos _
    have hamp : (121096 / 1000 : ℝ) < 1210961 / 10000 := by norm_num
    nlinarith

end MathlibPlus.Analysis
