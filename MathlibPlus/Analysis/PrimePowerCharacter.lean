import Mathlib

open scoped BigOperators

namespace MathlibPlus.Analysis.PrimePowerCharacter

/-- The amplitude-plus-phase square identity used in the prime-power character gap. -/
theorem hyperbolicCompactFactor_sumOfSquares (a θ : ℝ) (ha : 0 < a) :
    a + a⁻¹ - 2 * Real.cos θ =
      (Real.sqrt a - (Real.sqrt a)⁻¹) ^ 2 +
        Complex.normSq (1 - Complex.exp ((θ : ℂ) * Complex.I)) := by
  have hs : Real.sqrt a ≠ 0 := (Real.sqrt_ne_zero').2 ha
  have hs_sq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  rw [show Complex.normSq (1 - Complex.exp ((θ : ℂ) * Complex.I)) =
      2 - 2 * Real.cos θ by
    simp [Complex.normSq_apply, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
    nlinarith [Real.sin_sq_add_cos_sq θ]]
  field_simp
  rw [hs_sq]
  ring

end MathlibPlus.Analysis.PrimePowerCharacter

namespace MathlibPlus.Open.Analysis.PrimePowerCharacter

/-- For the split spectrum `(q, 1, q⁻¹)` and compact spectrum
`(exp(iφ), 1, exp(-iφ))`, the traces on every positive symmetric power have
the packet's exact weighted character difference, and that difference is positive.
The finite triple sums are the monomial-basis traces of the symmetric powers. -/
def sumOfSquaresGap : Prop :=
  ∀ (p k : ℕ) (φ : ℝ), Nat.Prime p → 1 ≤ k →
    let q : ℝ := (p : ℝ) ^ 11
    let e : ℝ := ∑ a ∈ Finset.range (k + 1),
      ∑ b ∈ Finset.range (k + 1),
        ∑ c ∈ Finset.range (k + 1),
          if a + b + c = k then q ^ a * (q ^ c)⁻¹ else 0
    let r : ℝ := ∑ a ∈ Finset.range (k + 1),
      ∑ b ∈ Finset.range (k + 1),
        ∑ c ∈ Finset.range (k + 1),
          if a + b + c = k then
            (Complex.exp ((φ : ℂ) * Complex.I) ^ a *
              Complex.exp (-((φ : ℂ) * Complex.I)) ^ c).re
          else 0
    e - r = ∑ m ∈ Finset.Icc 1 k,
      (((k - m) / 2 + 1 : ℕ) : ℝ) *
        (q ^ m + (q ^ m)⁻¹ - 2 * Real.cos ((m : ℝ) * φ)) ∧
      0 < e - r

end MathlibPlus.Open.Analysis.PrimePowerCharacter
