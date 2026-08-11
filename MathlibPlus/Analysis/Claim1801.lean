import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

namespace MathlibPlus.Analysis.Claim1801

/-- The exact denominator gaps and the resulting strict half-plane inclusions in claim 1801.

The zeta nonvanishing context of the source record is not part of this declaration: the
formal statement records the displayed arithmetic and the induced comparison of the two
real half-planes for every `t ≥ 2`. -/
theorem denominatorImprovements :
    (((4.824 : ℝ) - 4.82 = 1 / 250) ∧ 0 < (4.824 : ℝ) - 4.82) ∧
      (((4.862 : ℝ) - 4.82 = 21 / 500) ∧ 0 < (4.862 : ℝ) - 4.82) ∧
      (∀ t : ℝ, 2 ≤ t →
        ({σ : ℝ | σ > 1 - 1 / ((4.824 : ℝ) * Real.log t)} ⊂
          {σ : ℝ | σ > 1 - 1 / ((4.82 : ℝ) * Real.log t)}) ∧
        ({σ : ℝ | σ > 1 - 1 / ((4.862 : ℝ) * Real.log t)} ⊂
          {σ : ℝ | σ > 1 - 1 / ((4.82 : ℝ) * Real.log t)})) := by
  have strict_region :
      ∀ {d₁ d₂ : ℝ}, 0 < d₁ → d₁ < d₂ →
        ∀ t : ℝ, 2 ≤ t →
          {σ : ℝ | σ > 1 - 1 / (d₂ * Real.log t)} ⊂
            {σ : ℝ | σ > 1 - 1 / (d₁ * Real.log t)} := by
    intro d₁ d₂ hd₁ hd₁₂ t ht
    have hlog : 0 < Real.log t :=
      Real.log_pos (lt_of_lt_of_le (by norm_num) ht)
    have hden₁ : 0 < d₁ * Real.log t := mul_pos hd₁ hlog
    have hden₂ : 0 < d₂ * Real.log t :=
      mul_pos (lt_trans hd₁ hd₁₂) hlog
    have hden₁₂ : d₁ * Real.log t < d₂ * Real.log t := by
      nlinarith
    have hrecip : 1 / (d₂ * Real.log t) < 1 / (d₁ * Real.log t) :=
      one_div_lt_one_div_of_lt hden₁ hden₁₂
    have hthreshold :
        1 - 1 / (d₁ * Real.log t) < 1 - 1 / (d₂ * Real.log t) := by
      linarith
    refine Set.ssubset_iff_exists.mpr ⟨?_, ?_⟩
    · intro σ hσ
      change σ > 1 - 1 / (d₂ * Real.log t) at hσ
      change σ > 1 - 1 / (d₁ * Real.log t)
      linarith
    · let σ₀ : ℝ :=
        ((1 - 1 / (d₁ * Real.log t)) + (1 - 1 / (d₂ * Real.log t))) / 2
      refine ⟨σ₀, ?_, ?_⟩
      · change σ₀ > 1 - 1 / (d₁ * Real.log t)
        dsimp [σ₀]
        linarith
      · change ¬σ₀ > 1 - 1 / (d₂ * Real.log t)
        dsimp [σ₀]
        linarith
  have h₁ : (0 : ℝ) < 4.82 := by norm_num
  have h₁₂ : (4.82 : ℝ) < 4.824 := by norm_num
  have h₁₃ : (4.82 : ℝ) < 4.862 := by norm_num
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ?_⟩
  intro t ht
  exact ⟨strict_region h₁ h₁₂ t ht, strict_region h₁ h₁₃ t ht⟩

end MathlibPlus.Analysis.Claim1801
