import Mathlib

namespace MathlibPlus.Algebra.ElementaryArithmeticClaims

/-- Claim 15658.  The denominator is the squared distance from `(β, γ)` to
`(1, 0)`, and the displayed rate identity is an exact algebraic identity. -/
theorem cayleyRateIdentity (β γ : ℝ)
    (hD : (β - 1) ^ 2 + γ ^ 2 ≠ 0) :
    (β ^ 2 + γ ^ 2) / ((β - 1) ^ 2 + γ ^ 2) - 1 =
      (2 * β - 1) / ((β - 1) ^ 2 + γ ^ 2) := by
  field_simp [hD]
  ring

/-- Claim 14645.  The unspecified numerical domain is made explicit as `ℤ`,
which retains positivity, the divisibility assertion, and the integral Euler
characteristic without introducing any geometric hypotheses. -/
theorem arithmeticAdmissibility_4_20 :
    let c₁Sq : ℤ := 4
    let c₂ : ℤ := 20
    0 < c₁Sq ∧
      0 < c₂ ∧
      5 * c₁Sq ≥ c₂ - 36 ∧
      c₁Sq ≤ 3 * c₂ ∧
      12 ∣ c₁Sq + c₂ ∧
      (c₁Sq + c₂) / 12 = 2 := by
  norm_num

/-- Claim 27654.  “Both integers” is represented by integer witnesses for a
rational number and its inverse. -/
theorem reciprocalIntegerUnits (c : ℚ) (hc : c ≠ 0)
    (hc_int : ∃ a : ℤ, c = (a : ℚ))
    (hinv_int : ∃ b : ℤ, c⁻¹ = (b : ℚ)) :
    c = 1 ∨ c = -1 := by
  rcases hc_int with ⟨a, ha⟩
  rcases hinv_int with ⟨b, hb⟩
  have hprodQ : (a : ℚ) * (b : ℚ) = 1 := by
    rw [← ha, ← hb]
    exact mul_inv_cancel₀ hc
  have hprod : a * b = 1 := by
    exact_mod_cast hprodQ
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hprod with ha_one | ha_neg
  · left
    simpa [ha_one] using ha
  · right
    simpa [ha_neg] using ha

/-- Claim 35764.  The weight is taken in `ℝ`, the natural domain of the
strict inequalities in the source statement. -/
theorem dyadicWeightStrictDecrease :
    let w : ℕ → ℝ := fun j => (j : ℝ) / (2 : ℝ) ^ j
    w 1 = 1 / 2 ∧
      w 2 = 1 / 2 ∧
      ∀ j : ℕ, 2 ≤ j → w (j + 1) < w j := by
  dsimp
  constructor
  · norm_num
  constructor
  · norm_num
  · intro j hj
    have hj_real : (2 : ℝ) ≤ j := by
      exact_mod_cast hj
    have hpow : (0 : ℝ) < (2 : ℝ) ^ j := by
      positivity
    have hstep : ((j + 1 : ℕ) : ℝ) / 2 < (j : ℝ) := by
      norm_num [Nat.cast_add, Nat.cast_one]
      nlinarith
    calc
      ((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (j + 1) =
          (((j + 1 : ℕ) : ℝ) / 2) / (2 : ℝ) ^ j := by
            rw [pow_succ]
            field_simp
      _ < (j : ℝ) / (2 : ℝ) ^ j :=
        (div_lt_div_iff_of_pos_right hpow).2 hstep

end MathlibPlus.Algebra.ElementaryArithmeticClaims
