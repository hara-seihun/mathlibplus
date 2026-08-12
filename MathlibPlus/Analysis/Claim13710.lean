import Mathlib

namespace MathlibPlus.Analysis.Claim13710

/-- Exact minimum of the displayed Fourier symbol, with explicit minimizers in
both regimes.  The later operator/coercivity sentence in the packet is not
silently given a source-specific `L²` operator interface; its symbolic
`1/16` lower bound is retained. -/
theorem symbol_minimum
    (x : ℝ) :
    let p : ℝ → ℝ := fun τ => (x ^ 2 + 1 / 4 - τ ^ 2) ^ 2 + τ ^ 2
    (((|x| ≤ 1 / 2 →
        (∀ τ, (x ^ 2 + 1 / 4 - τ ^ 2) ^ 2 + τ ^ 2 ≥
          (x ^ 2 + 1 / 4) ^ 2) ∧
        p 0 = (x ^ 2 + 1 / 4) ^ 2) ∧
      (|x| ≥ 1 / 2 →
        (∀ τ, (x ^ 2 + 1 / 4 - τ ^ 2) ^ 2 + τ ^ 2 ≥ x ^ 2) ∧
        p (Real.sqrt (x ^ 2 - 1 / 4)) = x ^ 2)) ∧
      ∀ τ, (1 / 16 : ℝ) ≤ p τ) := by
  dsimp
  constructor
  · constructor
    · intro hx
      have hxsq : x ^ 2 ≤ (1 / 4 : ℝ) := by
        have h : |x| ≤ |(1 / 2 : ℝ)| := by simpa using hx
        have h' := (sq_le_sq).2 h
        norm_num at h' ⊢
        exact h'
      constructor
      · intro τ
        have hfactor : 0 ≤ τ ^ 2 + (1 / 2 : ℝ) - 2 * x ^ 2 := by
          nlinarith [sq_nonneg τ]
        have hprod : 0 ≤ τ ^ 2 * (τ ^ 2 + (1 / 2 : ℝ) - 2 * x ^ 2) :=
          mul_nonneg (sq_nonneg τ) hfactor
        nlinarith
      · ring
    · intro hx
      have hxsq : (1 / 4 : ℝ) ≤ x ^ 2 := by
        have h : |(1 / 2 : ℝ)| ≤ |x| := by simpa using hx
        have h' := (sq_le_sq).2 h
        norm_num at h' ⊢
        exact h'
      have hrad : 0 ≤ x ^ 2 - (1 / 4 : ℝ) := by linarith
      have hsqrt : (Real.sqrt (x ^ 2 - (1 / 4 : ℝ))) ^ 2 =
          x ^ 2 - (1 / 4 : ℝ) := Real.sq_sqrt hrad
      constructor
      · intro τ
        nlinarith [sq_nonneg (τ ^ 2 - (x ^ 2 - (1 / 4 : ℝ)))]
      · nlinarith
  · intro τ
    by_cases hx : |x| ≤ 1 / 2
    · have hxsq : x ^ 2 ≤ (1 / 4 : ℝ) := by
        have h : |x| ≤ |(1 / 2 : ℝ)| := by simpa using hx
        have h' := (sq_le_sq).2 h
        norm_num at h' ⊢
        exact h'
      have hfactor : 0 ≤ τ ^ 2 + (1 / 2 : ℝ) - 2 * x ^ 2 := by
        nlinarith [sq_nonneg τ]
      have hprod : 0 ≤ τ ^ 2 * (τ ^ 2 + (1 / 2 : ℝ) - 2 * x ^ 2) :=
        mul_nonneg (sq_nonneg τ) hfactor
      nlinarith [sq_nonneg x]
    · have hx' : (1 / 2 : ℝ) ≤ |x| := le_of_not_ge hx
      have hxsq : (1 / 4 : ℝ) ≤ x ^ 2 := by
        have h : |(1 / 2 : ℝ)| ≤ |x| := by simpa using hx'
        have h' := (sq_le_sq).2 h
        norm_num at h' ⊢
        exact h'
      nlinarith [sq_nonneg (τ ^ 2 - (x ^ 2 - (1 / 4 : ℝ)))]

end MathlibPlus.Analysis.Claim13710
