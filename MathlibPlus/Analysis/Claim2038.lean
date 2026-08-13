import Mathlib

namespace MathlibPlus.Analysis.Claim2038

/-- Claim 2038: decreasing either positive denominator coefficient strictly
increases the exceptional-zero reciprocal input and therefore cannot increase
its clipped upper-bound input. -/
theorem monotoneExceptionalZeroInput_claim2038
    (q : ℝ) (V : ℝ → ℝ) (t : ℝ) (B : ℝ)
    (c₁ c₂ c₁' c₂' : ℝ)
    (hq : 1 < q) (hV : 0 < V t)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hc₁' : 0 < c₁') (hc₂' : 0 < c₂')
    (h₁ : c₁' ≤ c₁) (h₂ : c₂' ≤ c₂)
    (hstrict : c₁' < c₁ ∨ c₂' < c₂) :
    let η := fun a b : ℝ => 1 / (a * Real.log q + b * V t)
    η c₁ c₂ < η c₁' c₂' ∧
      min B (1 - η c₁' c₂') ≤ min B (1 - η c₁ c₂) := by
  dsimp
  have hlog : 0 < Real.log q := Real.log_pos hq
  have hden : 0 < c₁ * Real.log q + c₂ * V t := by positivity
  have hden' : 0 < c₁' * Real.log q + c₂' * V t := by positivity
  have hden_lt : c₁' * Real.log q + c₂' * V t <
      c₁ * Real.log q + c₂ * V t := by
    rcases hstrict with h | h
    · have hfirst : c₁' * Real.log q < c₁ * Real.log q :=
        mul_lt_mul_of_pos_right h hlog
      have hsecond : c₂' * V t ≤ c₂ * V t :=
        mul_le_mul_of_nonneg_right h₂ (le_of_lt hV)
      nlinarith
    · have hfirst : c₁' * Real.log q ≤ c₁ * Real.log q :=
        mul_le_mul_of_nonneg_right h₁ (le_of_lt hlog)
      have hsecond : c₂' * V t < c₂ * V t :=
        mul_lt_mul_of_pos_right h hV
      nlinarith
  have heta : 1 / (c₁ * Real.log q + c₂ * V t) <
      1 / (c₁' * Real.log q + c₂' * V t) := by
    exact one_div_lt_one_div_of_lt hden' hden_lt
  have hclip : 1 - 1 / (c₁' * Real.log q + c₂' * V t) ≤
      1 - 1 / (c₁ * Real.log q + c₂ * V t) := by linarith
  exact ⟨heta, min_le_min_left B hclip⟩

end MathlibPlus.Analysis.Claim2038
