import Mathlib

namespace MathlibPlus.Analysis

/-- Claim 4543.  The displayed Evgrafov--Postnikov constant is positive, and
so is the corresponding fixed-order heat-action expression on its stated
positive-time, nonzero-space domain.  The formula is kept local here because
the packet does not supply a reusable heat-kernel definition. -/
theorem sigma_and_heatAction_pos_claim4543 (m : ℕ) (hm : 0 < m) :
    let mr : ℝ := m
    let sigma : ℝ :=
      (2 * mr - 1) * Real.rpow (2 * mr) (-(2 * mr) / (2 * mr - 1)) *
        Real.sin (Real.pi / (4 * mr - 2))
    0 < sigma ∧
      ∀ α x : ℝ, 0 < α → x ≠ 0 →
        0 < sigma * Real.rpow α (-1 / (2 * mr - 1)) *
          Real.rpow |x| ((2 * mr) / (2 * mr - 1)) := by
  dsimp
  have hm1n : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm)
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm1n
  have hden : 0 < 4 * (m : ℝ) - 2 := by
    nlinarith
  have hden2 : (2 : ℝ) ≤ 4 * (m : ℝ) - 2 := by
    nlinarith
  have hargpos : 0 < Real.pi / (4 * (m : ℝ) - 2) :=
    div_pos Real.pi_pos hden
  have hargle : Real.pi / (4 * (m : ℝ) - 2) ≤ Real.pi / 2 := by
    gcongr
  have harglt : Real.pi / (4 * (m : ℝ) - 2) < Real.pi := by
    calc
      Real.pi / (4 * (m : ℝ) - 2) ≤ Real.pi / 2 := hargle
      _ < Real.pi := by nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin (Real.pi / (4 * (m : ℝ) - 2)) :=
    Real.sin_pos_of_pos_of_lt_pi hargpos harglt
  have hbase : 0 < 2 * (m : ℝ) := by positivity
  have hfactor : 0 < 2 * (m : ℝ) - 1 := by
    nlinarith
  have hpow : 0 < Real.rpow (2 * (m : ℝ))
      (-(2 * (m : ℝ)) / (2 * (m : ℝ) - 1)) :=
    Real.rpow_pos_of_pos hbase _
  have hsigma :
      0 < (2 * (m : ℝ) - 1) *
          Real.rpow (2 * (m : ℝ))
            (-(2 * (m : ℝ)) / (2 * (m : ℝ) - 1)) *
          Real.sin (Real.pi / (4 * (m : ℝ) - 2)) := by
    exact mul_pos (mul_pos hfactor hpow) hsin
  refine ⟨hsigma, ?_⟩
  intro α x hα hx
  have hαpow : 0 < Real.rpow α (-1 / (2 * (m : ℝ) - 1)) :=
    Real.rpow_pos_of_pos hα _
  have hxabs : 0 < |x| := abs_pos.mpr hx
  have hxpow : 0 < Real.rpow |x| ((2 * (m : ℝ)) / (2 * (m : ℝ) - 1)) :=
    Real.rpow_pos_of_pos hxabs _
  exact mul_pos (mul_pos hsigma hαpow) hxpow

end MathlibPlus.Analysis
