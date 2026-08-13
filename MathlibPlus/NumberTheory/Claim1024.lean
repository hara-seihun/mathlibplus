import Mathlib

namespace MathlibPlus.NumberTheory.Claim1024

/-!
The packet's `|t| ≥ 3` convention is retained.  The open zero-free theorem is
passed as an explicit hypothesis, so this statement formalizes only the
boundary interiorization and the numerical ceiling, not an independent proof
of Yang's zeta theorem.
-/

/-- The open denominator `4.862` implies the closed `R* = 4.86201` region, and
`R*` lies below the stated FKS ceiling. -/
theorem yangOpenToClosed
    (zeta : ℂ → ℂ)
    (hopen : ∀ t : ℝ, 3 ≤ |t| → ∀ σ : ℝ,
      1 - 1 / (4.862 * Real.log |t|) < σ →
        zeta (σ + t * Complex.I) ≠ 0) :
    (∀ t : ℝ, 3 ≤ |t| → ∀ σ : ℝ,
      1 - 1 / (4.86201 * Real.log |t|) ≤ σ →
        zeta (σ + t * Complex.I) ≠ 0) ∧
      (4.86201 : ℝ) < 5.573412 := by
  refine ⟨?_, ?_⟩
  · intro t ht σ hσ
    have habs : (1 : ℝ) < |t| := lt_of_lt_of_le (by norm_num) ht
    have hlog : 0 < Real.log |t| := Real.log_pos habs
    have hden₀ : 0 < (4.862 : ℝ) * Real.log |t| := by
      exact mul_pos (by norm_num) hlog
    have hden : (4.862 : ℝ) * Real.log |t| <
        4.86201 * Real.log |t| := by
      exact mul_lt_mul_of_pos_right (by norm_num) hlog
    have hrecip : 1 / (4.86201 * Real.log |t|) <
        1 / ((4.862 : ℝ) * Real.log |t|) :=
      one_div_lt_one_div_of_lt hden₀ hden
    apply hopen t ht σ
    linarith
  · norm_num

end MathlibPlus.NumberTheory.Claim1024
