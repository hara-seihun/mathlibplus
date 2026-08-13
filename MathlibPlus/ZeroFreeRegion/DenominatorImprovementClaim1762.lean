import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

namespace MathlibPlus.ZeroFreeRegion

/-!
# Denominator improvement at 4.824 (claim 1762)

The source records the exact gaps from 4.824 to 4.83 and 4.825, together
with the resulting strict widening of the associated logarithmic half-planes.
The source-specific zero-free-region context is not part of this declaration.
-/

/-- The exact arithmetic and strict half-plane widening stated in claim 1762. -/
theorem denominatorImprovement_claim1762 :
    (((483 / 100 : ℝ) - 603 / 125 = 3 / 500) ∧ 0 < (3 / 500 : ℝ)) ∧
      (((193 / 40 : ℝ) - 603 / 125 = 1 / 1000) ∧ 0 < (1 / 1000 : ℝ)) ∧
      (∀ t : ℝ, 1 < t →
        ({σ : ℝ | σ > 1 - 1 / ((483 / 100 : ℝ) * Real.log t)} ⊂
          {σ : ℝ | σ > 1 - 1 / ((603 / 125 : ℝ) * Real.log t)}) ∧
        ({σ : ℝ | σ > 1 - 1 / ((193 / 40 : ℝ) * Real.log t)} ⊂
          {σ : ℝ | σ > 1 - 1 / ((603 / 125 : ℝ) * Real.log t)})) := by
  have strict_region :
      ∀ {dsmall dlarge : ℝ}, 0 < dsmall → dsmall < dlarge →
        ∀ t : ℝ, 1 < t →
          {σ : ℝ | σ > 1 - 1 / (dlarge * Real.log t)} ⊂
            {σ : ℝ | σ > 1 - 1 / (dsmall * Real.log t)} := by
    intro dsmall dlarge hdsmall hgap t ht
    have hlog : 0 < Real.log t := Real.log_pos ht
    have hsmall : 0 < dsmall * Real.log t := mul_pos hdsmall hlog
    have hlarge : 0 < dlarge * Real.log t :=
      mul_pos (lt_trans hdsmall hgap) hlog
    have hden : dsmall * Real.log t < dlarge * Real.log t := by
      exact mul_lt_mul_of_pos_right hgap hlog
    have hrecip : 1 / (dlarge * Real.log t) < 1 / (dsmall * Real.log t) :=
      one_div_lt_one_div_of_lt hsmall hden
    have hthreshold :
        1 - 1 / (dsmall * Real.log t) <
          1 - 1 / (dlarge * Real.log t) := by
      linarith
    refine Set.ssubset_iff_exists.mpr ⟨?_, ?_⟩
    · intro σ hσ
      change σ > 1 - 1 / (dlarge * Real.log t) at hσ
      change σ > 1 - 1 / (dsmall * Real.log t)
      linarith
    · let σ₀ : ℝ :=
        ((1 - 1 / (dsmall * Real.log t)) +
          (1 - 1 / (dlarge * Real.log t))) / 2
      refine ⟨σ₀, ?_, ?_⟩
      · change σ₀ > 1 - 1 / (dsmall * Real.log t)
        dsimp [σ₀]
        linarith
      · change ¬σ₀ > 1 - 1 / (dlarge * Real.log t)
        dsimp [σ₀]
        linarith
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ?_⟩
  intro t ht
  exact ⟨strict_region (by norm_num) (by norm_num) t ht,
    strict_region (by norm_num) (by norm_num) t ht⟩

end MathlibPlus.ZeroFreeRegion
