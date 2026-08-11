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

end MathlibPlus.NumberTheory
