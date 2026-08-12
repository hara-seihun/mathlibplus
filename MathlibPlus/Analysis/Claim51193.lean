import Mathlib

namespace MathlibPlus.Analysis.Claim51193

theorem competitiveRatio_identity_claim51193 (n : ℕ) (hn : 0 < n) :
    ((n : ℚ) / 16) / ((11 * (n : ℚ) + 5) / (32 * (n : ℚ))) =
      (2 * (n : ℚ) ^ 2) / (11 * (n : ℚ) + 5) := by
  field_simp
  ring

theorem competitiveRatio_unbounded_claim51193 :
    ∀ C : ℚ, ∃ n : ℕ,
      C < (2 * (n : ℚ) ^ 2) / (11 * (n : ℚ) + 5) := by
  intro C
  obtain ⟨n, hn⟩ := exists_nat_gt (8 * C)
  refine ⟨max n 1, ?_⟩
  have hm_one : 1 ≤ max n 1 := Nat.le_max_right n 1
  have hnpos : (0 : ℚ) < (max n 1 : ℕ) := by
    exact_mod_cast (Nat.zero_lt_one.trans_le hm_one)
  have hlarge : 8 * C < (max n 1 : ℚ) := by
    exact lt_of_lt_of_le hn (by exact_mod_cast (Nat.le_max_left n 1))
  have hratio :
      ((max n 1 : ℕ) : ℚ) / 8 ≤
        (2 * ((max n 1 : ℕ) : ℚ) ^ 2) /
          (11 * ((max n 1 : ℕ) : ℚ) + 5) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℚ) < 8)
      (by positivity : (0 : ℚ) < 11 * ((max n 1 : ℕ) : ℚ) + 5)).mpr
    nlinarith [show (1 : ℚ) ≤ (max n 1 : ℕ) by exact_mod_cast hm_one]
  have hC : C < ((max n 1 : ℕ) : ℚ) / 8 := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℚ) < 8)).mpr
    simpa [mul_comm] using hlarge
  exact lt_of_lt_of_le hC hratio

end MathlibPlus.Analysis.Claim51193
