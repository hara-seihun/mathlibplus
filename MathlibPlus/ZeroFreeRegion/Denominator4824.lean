import Mathlib

/-!
# Exact zero-free-region denominator improvement to 4.824

This file formalizes the standalone arithmetic and boundary comparison in Record 2
of source record `C-0113`. It does not assert a Riemann-zeta zero-free theorem.
-/

namespace MathlibPlus.ZeroFreeRegion

/-- The denominator `4.824` is smaller than `4.83` by `3/500` and smaller than
`4.825` by `1/1000`; consequently its classical zero-free boundary is strictly to
the left of both comparison boundaries at every height `t > 1`. -/
theorem denominator4824Improvement :
    (483 / 100 : ℝ) - 603 / 125 = 3 / 500 ∧
    (0 : ℝ) < 3 / 500 ∧
    (193 / 40 : ℝ) - 603 / 125 = 1 / 1000 ∧
    (0 : ℝ) < 1 / 1000 ∧
    ∀ t : ℝ, 1 < t →
      1 - 1 / ((603 / 125 : ℝ) * Real.log t) <
        1 - 1 / ((483 / 100 : ℝ) * Real.log t) ∧
      1 - 1 / ((603 / 125 : ℝ) * Real.log t) <
        1 - 1 / ((193 / 40 : ℝ) * Real.log t) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  intro t ht
  have hlog : 0 < Real.log t := Real.log_pos ht
  constructor
  · have hsmall : 0 < (603 / 125 : ℝ) * Real.log t :=
      mul_pos (by norm_num) hlog
    have hlarge : 0 < (483 / 100 : ℝ) * Real.log t :=
      mul_pos (by norm_num) hlog
    have hrecip :
        1 / ((483 / 100 : ℝ) * Real.log t) <
          1 / ((603 / 125 : ℝ) * Real.log t) := by
      rw [div_lt_div_iff₀ hlarge hsmall]
      nlinarith
    linarith
  · have hsmall : 0 < (603 / 125 : ℝ) * Real.log t :=
      mul_pos (by norm_num) hlog
    have hlarge : 0 < (193 / 40 : ℝ) * Real.log t :=
      mul_pos (by norm_num) hlog
    have hrecip :
        1 / ((193 / 40 : ℝ) * Real.log t) <
          1 / ((603 / 125 : ℝ) * Real.log t) := by
      rw [div_lt_div_iff₀ hlarge hsmall]
      nlinarith
    linarith


/-- Claim 1008's denominator/amplitude convention and its strict region
monotonicity.  This records the vocabulary and the logical nesting of the
zero-free regions without asserting a new zeta zero-free theorem. -/
theorem classicalRegionDenominatorMonotonicity_claim1008
    (H Rsmall Rlarge : ℝ)
    (hH : 1 < H) (hsmall : 0 < Rsmall) (hlarge : Rsmall < Rlarge) :
    (1 / Rlarge < 1 / Rsmall) ∧
      (∀ t : ℝ, H ≤ t →
        1 - 1 / (Rsmall * Real.log t) <
          1 - 1 / (Rlarge * Real.log t)) ∧
      ((∀ (t σ : ℝ), H ≤ t →
          1 - 1 / (Rsmall * Real.log t) < σ →
          riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) →
        ∀ (t σ : ℝ), H ≤ t →
          1 - 1 / (Rlarge * Real.log t) < σ →
          riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) := by
  have hRlarge : 0 < Rlarge := lt_trans hsmall hlarge
  constructor
  · rw [div_lt_div_iff₀ hRlarge hsmall]
    nlinarith
  constructor
  · intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le hH ht
    have hlog : 0 < Real.log t := Real.log_pos ht1
    have hsmallD : 0 < Rsmall * Real.log t := mul_pos hsmall hlog
    have hlargeD : 0 < Rlarge * Real.log t := mul_pos hRlarge hlog
    have hrecip :
        1 / (Rlarge * Real.log t) <
          1 / (Rsmall * Real.log t) := by
      rw [div_lt_div_iff₀ hlargeD hsmallD]
      nlinarith
    linarith
  · intro hvalid t σ ht hσ
    apply hvalid t σ ht
    have ht1 : 1 < t := lt_of_lt_of_le hH ht
    have hlog : 0 < Real.log t := Real.log_pos ht1
    have hsmallD : 0 < Rsmall * Real.log t := mul_pos hsmall hlog
    have hlargeD : 0 < Rlarge * Real.log t := mul_pos hRlarge hlog
    have hrecip :
        1 / (Rlarge * Real.log t) <
          1 / (Rsmall * Real.log t) := by
      rw [div_lt_div_iff₀ hlargeD hsmallD]
      nlinarith
    linarith

end MathlibPlus.ZeroFreeRegion
