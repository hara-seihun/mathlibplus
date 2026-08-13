import Mathlib

namespace MathlibPlus.Analysis

/-- The local factor in admitted claim 14092 has modulus greater than one in the
open critical strip, so its subtraction from one cannot vanish. -/
theorem etaLocalNumerator_ne_zero_claim14092
    (ω : ℕ → ℂ) (s : ℂ)
    (_hs_lower : (1 / 2 : ℝ) < s.re)
    (hs_upper : s.re < 1)
    (hω : ‖ω 2‖ = 1) :
    ‖((2 : ℝ) : ℂ) * ω 2 * ((2 : ℝ) : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (1 - s.re) ∧
      1 < (2 : ℝ) ^ (1 - s.re) ∧
      1 - ((2 : ℝ) : ℂ) * ω 2 * ((2 : ℝ) : ℂ) ^ (-s) ≠ 0 := by
  have hnorm_cpow : ‖((2 : ℝ) : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re) := by
    simpa only [Complex.neg_re] using
      (Complex.norm_cpow_eq_rpow_re_of_pos (x := (2 : ℝ))
        (by norm_num : (0 : ℝ) < 2) (-s))
  have hnorm :
      ‖((2 : ℝ) : ℂ) * ω 2 * ((2 : ℝ) : ℂ) ^ (-s)‖ =
        2 * (2 : ℝ) ^ (-s.re) := by
    rw [norm_mul, norm_mul, hω, hnorm_cpow]
    norm_num
  have hrpow :
      (2 : ℝ) ^ (1 - s.re) = 2 * (2 : ℝ) ^ (-s.re) := by
    calc
      (2 : ℝ) ^ (1 - s.re) = (2 : ℝ) ^ (-s.re + 1) := by
        congr 1
        ring
      _ = (2 : ℝ) ^ (-s.re) * (2 : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ = 2 * (2 : ℝ) ^ (-s.re) := by
        rw [Real.rpow_one]
        ring
  have hnorm_eq :
      ‖((2 : ℝ) : ℂ) * ω 2 * ((2 : ℝ) : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (1 - s.re) := by
    rw [hnorm, hrpow]
  have hexp : 0 < 1 - s.re := by linarith
  have hgt : 1 < (2 : ℝ) ^ (1 - s.re) := by
    exact Real.one_lt_rpow (by norm_num) hexp
  refine ⟨hnorm_eq, hgt, ?_⟩
  intro hzero
  have hunit : ((2 : ℝ) : ℂ) * ω 2 * ((2 : ℝ) : ℂ) ^ (-s) = 1 := by
    exact (sub_eq_zero.mp hzero).symm
  have hnorm_one : ‖((2 : ℝ) : ℂ) * ω 2 * ((2 : ℝ) : ℂ) ^ (-s)‖ = 1 := by
    simpa using congrArg norm hunit
  linarith

end MathlibPlus.Analysis
