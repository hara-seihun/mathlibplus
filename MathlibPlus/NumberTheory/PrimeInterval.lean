import Mathlib

namespace MathlibPlus.NumberTheory

/-- Claim 1296: strict containment of the first two terms of the binomial
expansion, together with the stated prime-interval consequence. -/
theorem strictBinomialContainment_69 :
    ∀ n : ℤ, 1 ≤ n →
      n ^ 69 + 69 * n ^ 68 < (n + 1) ^ 69 ∧
        ∀ p : ℤ, Prime p →
          n ^ 69 < p → p ≤ n ^ 69 + 69 * n ^ 68 → p < (n + 1) ^ 69 := by
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  have hbern :
      1 + (68 : ℝ) * (1 / (n : ℝ)) ≤
        (1 + 1 / (n : ℝ)) ^ (68 : ℕ) := by
    apply one_add_mul_le_pow
    have hrecip : 0 ≤ (1 / (n : ℝ)) := le_of_lt (one_div_pos.mpr hn0)
    nlinarith
  have hstrict :
      1 + (69 : ℝ) * (1 / (n : ℝ)) <
        (1 + 1 / (n : ℝ)) ^ (69 : ℕ) := by
    calc
      1 + (69 : ℝ) * (1 / (n : ℝ)) <
          (1 + 1 / (n : ℝ)) * (1 + (68 : ℝ) * (1 / (n : ℝ))) := by
            field_simp
            nlinarith [hn0]
      _ ≤ (1 + 1 / (n : ℝ)) * (1 + 1 / (n : ℝ)) ^ (68 : ℕ) := by
            gcongr
      _ = (1 + 1 / (n : ℝ)) ^ (69 : ℕ) := by ring
  have hreal :
      (n : ℝ) ^ 69 + 69 * (n : ℝ) ^ 68 < ((n : ℝ) + 1) ^ 69 := by
    have hn_pow : (0 : ℝ) < (n : ℝ) ^ 69 := by positivity
    have hrewrite :
        ((n : ℝ) + 1) ^ 69 = (n : ℝ) ^ 69 *
          (1 + 1 / (n : ℝ)) ^ 69 := by
      field_simp
    rw [hrewrite]
    have hscale := (mul_lt_mul_of_pos_left hstrict hn_pow)
    field_simp at hscale ⊢
    nlinarith
  have hcontain : n ^ 69 + 69 * n ^ 68 < (n + 1) ^ 69 := by
    exact_mod_cast hreal
  constructor
  · exact hcontain
  · intro p hp hnp hupper
    exact lt_of_le_of_lt hupper hcontain

/-- Claim 942: the derivative of the order-`n` prime-interval endpoint. -/
theorem derivativePrimeIntervalEndpoint (n : ℕ) (B x : ℝ) (hx : 1 < x) :
    deriv (fun y : ℝ => y * (1 + B / (Real.log y) ^ n)) x =
      1 + B * (Real.log x - n) / (Real.log x) ^ (n + 1) := by
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hpow := (Real.hasDerivAt_log hx0).pow n
  have hinv := hpow.inv (pow_ne_zero n hlog0)
  have hterm := hinv.const_mul B
  have hsum := (hasDerivAt_const x (1 : ℝ)).add hterm
  have hprod := (hasDerivAt_id x).mul hsum
  have hfun :
      (fun y : ℝ => y * (1 + B / (Real.log y) ^ n)) =
        id * ((fun _ : ℝ => (1 : ℝ)) + fun y => B * (Real.log y ^ n)⁻¹) := by
    funext y
    simp only [Pi.mul_apply, Pi.add_apply, id_eq, div_eq_mul_inv]
  rw [hfun]
  have hcancel :
      (n : ℝ) * Real.log x ^ (n - 1) * Real.log x =
        (n : ℝ) * Real.log x ^ n := by
    by_cases hn : n = 0
    · simp [hn]
    · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      calc
        (n : ℝ) * Real.log x ^ (n - 1) * Real.log x =
            (n : ℝ) * (Real.log x ^ (n - 1) * Real.log x) := by ring
        _ = (n : ℝ) * Real.log x ^ ((n - 1) + 1) := by rw [pow_succ]
        _ = (n : ℝ) * Real.log x ^ n := by rw [Nat.sub_add_cancel hnpos]
  have hcancelB :
      B * (n : ℝ) * Real.log x ^ (n - 1) * Real.log x =
        B * (n : ℝ) * Real.log x ^ n := by
    calc
      B * (n : ℝ) * Real.log x ^ (n - 1) * Real.log x =
          B * ((n : ℝ) * Real.log x ^ (n - 1) * Real.log x) := by ring
      _ = B * ((n : ℝ) * Real.log x ^ n) := by rw [hcancel]
      _ = B * (n : ℝ) * Real.log x ^ n := by ring
  have hderiv := hprod.deriv
  simp only [Pi.add_apply, Pi.inv_apply, Pi.pow_apply, id_eq,
    div_eq_mul_inv] at hderiv
  rw [hderiv]
  field_simp [hlog0, hx0]
  simp only [mul_zero]
  rw [pow_succ]
  rw [pow_succ]
  simp only [pow_one]
  calc
    (Real.log x ^ n * (Real.log x ^ n + B) +
        (0 + -(B * (n : ℝ) * Real.log x ^ (n - 1)))) *
        (Real.log x ^ n * Real.log x) =
      Real.log x ^ n * (Real.log x ^ n + B) *
          (Real.log x ^ n * Real.log x) -
        (B * (n : ℝ) * Real.log x ^ (n - 1) * Real.log x) *
          Real.log x ^ n := by ring
    _ = Real.log x ^ n * (Real.log x ^ n + B) *
          (Real.log x ^ n * Real.log x) -
        (B * (n : ℝ) * Real.log x ^ n) * Real.log x ^ n := by
          rw [hcancelB]
    _ = Real.log x ^ n * Real.log x ^ n *
          (Real.log x ^ n * Real.log x + B * (Real.log x - (n : ℝ))) := by
          ring

end MathlibPlus.NumberTheory
