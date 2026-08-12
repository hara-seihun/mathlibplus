import Mathlib

namespace MathlibPlus.Analysis

/-- Claim 1523: the printed `B₂`/`σ` pair has native decay below `0.1853`,
and the exponential tail hypothesis gives the corrected explicit-formula
remainder bound. -/
theorem claim1523_printedTailDefects :
    let B₂ : ℚ := 0.18525
    let σ : ℚ := 0.9999932
    let native : ℚ := B₂ * (8 * σ - 5) / 3
    let target : ℚ := 0.1853
    native = 0.1852466408 ∧ native < target ∧
      ∀ (L r T : ℝ), 0 ≤ L → 0 ≤ r →
        Real.exp ((B₂ : ℝ) * r) ≤ T →
        4.3128 * Real.rpow L (3 / 5 : ℝ) / T ≤
          4.3128 * Real.rpow L (3 / 5 : ℝ) *
            Real.exp (-((B₂ : ℝ) * r)) := by
  dsimp
  constructor
  · norm_num
  constructor
  · norm_num
  · intro L r T hL _hr hT
    have hE : 0 < Real.exp ((0.18525 : ℝ) * r) := Real.exp_pos _
    have hTpos : 0 < T := lt_of_lt_of_le hE hT
    have hinv : T⁻¹ ≤ Real.exp (-((0.18525 : ℝ) * r)) := by
      have h := (inv_le_inv₀ hTpos hE).2 hT
      simpa [← Real.exp_neg] using h
    have hpow : 0 ≤ Real.rpow L (3 / 5 : ℝ) := Real.rpow_nonneg hL _
    have hcoef : 0 ≤ (4.3128 : ℝ) * Real.rpow L (3 / 5 : ℝ) :=
      mul_nonneg (by norm_num) hpow
    calc
      4.3128 * Real.rpow L (3 / 5 : ℝ) / T =
          (4.3128 * Real.rpow L (3 / 5 : ℝ)) * T⁻¹ := by ring
      _ ≤ (4.3128 * Real.rpow L (3 / 5 : ℝ)) *
            Real.exp (-((0.18525 : ℝ) * r)) :=
        mul_le_mul_of_nonneg_left hinv hcoef

end MathlibPlus.Analysis
