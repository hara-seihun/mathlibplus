import Mathlib

namespace MathlibPlus.Analysis

/-- Claim 44901 (S1): the displayed exact witness has `K < R < 2K`.
The values of `y` and `N` are retained in the `let` chain even though the
reported inequality does not use them. -/
theorem exactWitnessS1_claim44901 :
    let t : ℝ := 1037 / 20000
    let y : ℝ := 31 / 100
    let K : ℝ := 690988
    let N : ℝ := 1380287
    let x : ℝ := 4 * Real.pi * (2 * K ^ 2 - t / 16) - 333609 / 2048
    let R : ℝ := Real.sqrt (x / (4 * Real.pi) + t / 16)
    K < R ∧ R < 2 * K := by
  dsimp
  let K : ℝ := 690988
  let rad : ℝ :=
    (4 * Real.pi * (2 * K ^ 2 - (1037 / 20000 : ℝ) / 16) -
        333609 / 2048) / (4 * Real.pi) + (1037 / 20000 : ℝ) / 16
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hrad_eq : rad = 2 * K ^ 2 - 333609 / (8192 * Real.pi) := by
    dsimp [rad, K]
    field_simp [ne_of_gt hpi]
    ring
  have hsmall : 333609 / (8192 * Real.pi) < K ^ 2 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 8192 * Real.pi)).2
    dsimp [K]
    nlinarith
  have hpos : 0 < 333609 / (8192 * Real.pi) := by positivity
  have hrad_lower : K ^ 2 < rad := by rw [hrad_eq]; nlinarith
  have hrad_nonneg : 0 ≤ rad := le_of_lt (lt_trans (by positivity) hrad_lower)
  have hrad_upper : rad < (2 * K) ^ 2 := by rw [hrad_eq]; nlinarith
  have hsqrt : (Real.sqrt rad) ^ 2 = rad := Real.sq_sqrt hrad_nonneg
  have hsqrt_nonneg : 0 ≤ Real.sqrt rad := Real.sqrt_nonneg _
  change K < Real.sqrt rad ∧ Real.sqrt rad < 2 * K
  constructor <;> nlinarith

end MathlibPlus.Analysis
