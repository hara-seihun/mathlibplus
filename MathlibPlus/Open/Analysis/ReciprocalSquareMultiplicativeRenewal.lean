import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Reciprocal-square multiplicative renewal for the classical Riesz field. -/
def reciprocalSquareMultiplicativeRenewal : Prop :=
  ∀ (x : ℝ),
    (hx : 0 < x) →
      let R : {y : ℝ // 0 < y} → ℝ := fun y =>
        y.1 *
          ∑' n : PNat,
            ((ArithmeticFunction.moebius (n : ℕ) : ℤ) : ℝ) *
              ((n : ℝ) ^ 2)⁻¹ *
              Real.exp (-y.1 / (n : ℝ) ^ 2)
      ∑' m : PNat,
        R (⟨x / (m : ℝ) ^ 2, by
          have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast m.property
          exact div_pos hx (pow_pos hm 2)⟩ : {y : ℝ // 0 < y}) =
          x * Real.exp (-x)

end MathlibPlus.Open.Analysis
