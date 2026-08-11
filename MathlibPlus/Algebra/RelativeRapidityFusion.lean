import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace MathlibPlus.Algebra.RelativeRapidityFusion

/--
Claim 6855.  The two relative-rapidity channels have the exact Lorentz
identity, the hyperbolic subtraction law, and a strict denominator bound.
-/
theorem relativeRapidityFusionIdentities_claim6855 (ξ₁ ξ₂ : ℝ) :
    let r₁ := Real.tanh ξ₁
    let r₂ := Real.tanh ξ₂
    let E := 1 - r₁ * r₂
    let O := r₂ - r₁
    E ^ 2 - O ^ 2 = (1 - r₁ ^ 2) * (1 - r₂ ^ 2) ∧
      0 < (1 - r₁ ^ 2) * (1 - r₂ ^ 2) ∧
      O / E = Real.tanh (ξ₂ - ξ₁) ∧
      |O| < E := by
  dsimp
  have ht1lt : Real.tanh ξ₁ < 1 := Real.tanh_lt_one ξ₁
  have ht1gt : -1 < Real.tanh ξ₁ := Real.neg_one_lt_tanh ξ₁
  have ht2lt : Real.tanh ξ₂ < 1 := Real.tanh_lt_one ξ₂
  have ht2gt : -1 < Real.tanh ξ₂ := Real.neg_one_lt_tanh ξ₂
  have hprod : Real.tanh ξ₁ * Real.tanh ξ₂ < 1 := by
    by_cases hx : 0 ≤ Real.tanh ξ₁
    · by_cases hx0 : 0 < Real.tanh ξ₁
      · have hxy : Real.tanh ξ₁ * Real.tanh ξ₂ < Real.tanh ξ₁ * 1 :=
          mul_lt_mul_of_pos_left ht2lt hx0
        nlinarith
      · have hx0' : Real.tanh ξ₁ = 0 := le_antisymm (not_lt.mp hx0) hx
        simp [hx0']
    · have hx0 : Real.tanh ξ₁ < 0 := lt_of_not_ge hx
      have hxy : Real.tanh ξ₁ * Real.tanh ξ₂ < Real.tanh ξ₁ * (-1) :=
        mul_lt_mul_of_neg_left ht2gt hx0
      nlinarith
  have hE : 0 < 1 - Real.tanh ξ₁ * Real.tanh ξ₂ := sub_pos.mpr hprod
  have h1 : 0 < 1 - (Real.tanh ξ₁) ^ 2 := by nlinarith
  have h2 : 0 < 1 - (Real.tanh ξ₂) ^ 2 := by nlinarith
  constructor
  · ring
  constructor
  · exact mul_pos h1 h2
  constructor
  · rw [Real.tanh_eq_sinh_div_cosh (ξ₁), Real.tanh_eq_sinh_div_cosh (ξ₂)]
    calc
      (Real.sinh ξ₂ / Real.cosh ξ₂ - Real.sinh ξ₁ / Real.cosh ξ₁) /
          (1 - (Real.sinh ξ₁ / Real.cosh ξ₁) *
            (Real.sinh ξ₂ / Real.cosh ξ₂)) =
          (Real.sinh ξ₂ * Real.cosh ξ₁ - Real.cosh ξ₂ * Real.sinh ξ₁) /
            (Real.cosh ξ₁ * Real.cosh ξ₂ - Real.sinh ξ₁ * Real.sinh ξ₂) := by
              field_simp [ne_of_gt (Real.cosh_pos ξ₁), ne_of_gt (Real.cosh_pos ξ₂)]
      _ = Real.tanh (ξ₂ - ξ₁) := by
        rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_sub, Real.cosh_sub]
        ring
  · apply (abs_lt).2
    constructor
    · have hleft :
          (1 + Real.tanh ξ₁) * Real.tanh ξ₂ < (1 + Real.tanh ξ₁) * 1 :=
        mul_lt_mul_of_pos_left ht2lt (by linarith)
      nlinarith
    · have hright :
          Real.tanh ξ₁ * (Real.tanh ξ₂ + 1) < 1 * (Real.tanh ξ₂ + 1) :=
        mul_lt_mul_of_pos_right ht1lt (by linarith)
      nlinarith

end MathlibPlus.Algebra.RelativeRapidityFusion
