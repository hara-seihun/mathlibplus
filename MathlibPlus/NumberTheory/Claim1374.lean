import Mathlib

namespace MathlibPlus.NumberTheory

/-- Admitted claim 1374: the first two terms of the binomial expansion are
strictly below the full power for every positive natural input. -/
theorem strictBinomialContainment_64 :
    ∀ n : ℕ, 1 ≤ n → n ^ 64 + 64 * n ^ 63 < (n + 1) ^ 64 := by
  intro n hn
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  have hbern :
      1 + (63 : ℝ) * (1 / (n : ℝ)) ≤
        (1 + 1 / (n : ℝ)) ^ (63 : ℕ) := by
    apply one_add_mul_le_pow
    have hrecip : 0 ≤ (1 / (n : ℝ)) := le_of_lt (one_div_pos.mpr hn0)
    nlinarith
  have hstrict :
      1 + (64 : ℝ) * (1 / (n : ℝ)) <
        (1 + 1 / (n : ℝ)) ^ (64 : ℕ) := by
    calc
      1 + (64 : ℝ) * (1 / (n : ℝ)) <
          (1 + 1 / (n : ℝ)) * (1 + (63 : ℝ) * (1 / (n : ℝ))) := by
            field_simp
            nlinarith [hn0]
      _ ≤ (1 + 1 / (n : ℝ)) * (1 + 1 / (n : ℝ)) ^ (63 : ℕ) := by
            gcongr
      _ = (1 + 1 / (n : ℝ)) ^ (64 : ℕ) := by ring
  have hreal :
      (n : ℝ) ^ 64 + 64 * (n : ℝ) ^ 63 < ((n : ℝ) + 1) ^ 64 := by
    have hn_pow : (0 : ℝ) < (n : ℝ) ^ 64 := by positivity
    have hrewrite :
        ((n : ℝ) + 1) ^ 64 = (n : ℝ) ^ 64 *
          (1 + 1 / (n : ℝ)) ^ 64 := by
      field_simp
    rw [hrewrite]
    have hscale := (mul_lt_mul_of_pos_left hstrict hn_pow)
    field_simp at hscale ⊢
    nlinarith
  exact_mod_cast hreal

end MathlibPlus.NumberTheory
