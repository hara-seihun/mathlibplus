import Mathlib

namespace MathlibPlus.Analysis.Claim22006

/--
The abstract minimax ratio bound from claim 22006.  Here “relative scalar
error at most `ε`” is formalized as `|ρ - 1| ≤ ε` for each positive ratio.
-/
theorem abstractMinimaxRatio_claim22006
    (ρ₁ ρ₂ ε : ℝ)
    (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) :
    (|ρ₁ - 1| ≤ ε → |ρ₂ - 1| ≤ ε →
        ρ₂ / ρ₁ ≤ (1 + ε) / (1 - ε)) ∧
      (ρ₂ / ρ₁ > (1 + ε) / (1 - ε) →
        |ρ₁ - 1| > ε ∨ |ρ₂ - 1| > ε) ∧
      (1 + (1 / 11 : ℝ)) / (1 - (1 / 11 : ℝ)) = 6 / 5 := by
  have hden : 0 < 1 - ε := by linarith
  have hbound :
      ∀ {x y : ℝ}, 0 < x → 0 < y → |x - 1| ≤ ε → |y - 1| ≤ ε →
        y / x ≤ (1 + ε) / (1 - ε) := by
    intro x y hx hy hxe hye
    have hx_lower : 1 - ε ≤ x := by
      have h := (abs_le.mp hxe).1
      linarith
    have hy_upper : y ≤ 1 + ε := by
      have h := (abs_le.mp hye).2
      linarith
    calc
      y / x ≤ (1 + ε) / x :=
        div_le_div_of_nonneg_right hy_upper (le_of_lt hx)
      _ ≤ (1 + ε) / (1 - ε) := by
        apply (div_le_div_iff₀ hx hden).2
        exact mul_le_mul_of_nonneg_left hx_lower (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · exact hbound hρ₁ hρ₂
  · intro hratio
    by_contra hnot
    have h₁ : |ρ₁ - 1| ≤ ε := by
      by_contra h
      exact hnot (Or.inl (lt_of_not_ge h))
    have h₂ : |ρ₂ - 1| ≤ ε := by
      by_contra h
      exact hnot (Or.inr (lt_of_not_ge h))
    exact (not_lt_of_ge (hbound hρ₁ hρ₂ h₁ h₂)) hratio
  · norm_num

end MathlibPlus.Analysis.Claim22006
