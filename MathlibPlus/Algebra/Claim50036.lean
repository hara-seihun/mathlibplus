import Mathlib

namespace MathlibPlus.Algebra.Claim50036

/-- The reserve polynomial in claim 50036, evaluated over exact rationals. -/
def rtilde (n : ℕ) : ℚ :=
  (55 * (n : ℚ) ^ 2 - 49 * (n : ℚ) - 6) / 32

/-- The diagonal quantity displayed in claim 50036. -/
def dVal (n : ℕ) : ℚ :=
  (101 * (n : ℚ) ^ 2 - (n : ℚ) - 100) / 128

/-- The off-diagonal quantity displayed in claim 50036. -/
def oVal (n : ℕ) : ℚ :=
  (141 * (n : ℚ) ^ 2 - 109 * (n : ℚ) - 88) / 128

/-- The structured-family value in claim 50036. -/
def psi (n : ℕ) : ℚ :=
  (141 * (n : ℚ) ^ 2 - 149 * (n : ℚ) + 20 - 12 / (n : ℚ)) / 128

/-- The root variance in the prefix formula of claim 50036. -/
def varRoot (n : ℕ) : ℚ :=
  (5 * (n : ℚ) ^ 2 + 11 * (n : ℚ)) / 16

/-- The prefix area in the reserve formula of claim 50036. -/
def prefixArea (n : ℕ) : ℚ :=
  (25 * (n : ℚ) ^ 2 + 49 * (n : ℚ) + 6) / 32

/-- The exact difference factorization in claim 50036. -/
theorem psi_sub_rtilde (n : ℕ) (hn : 0 < n) :
    psi n - rtilde n =
      -(((n : ℚ) - 1) * (79 * (n : ℚ) ^ 2 + 32 * (n : ℚ) - 12)) /
        (128 * (n : ℚ)) := by
  have hnq : (n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  dsimp [psi, rtilde]
  field_simp [hnq]
  ring

/-- The difference is strictly negative from `n = 2` onward. -/
theorem psi_sub_rtilde_negative (n : ℕ) (hn : 2 ≤ n) :
    psi n - rtilde n < 0 := by
  have hnpos : 0 < n := by omega
  have hnq : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hnm : 0 < (n : ℚ) - 1 := by linarith
  have hpoly : 0 < 79 * (n : ℚ) ^ 2 + 32 * (n : ℚ) - 12 := by
    nlinarith [sq_nonneg (n : ℚ)]
  rw [psi_sub_rtilde n hnpos]
  have hnum : 0 < ((n : ℚ) - 1) *
      (79 * (n : ℚ) ^ 2 + 32 * (n : ℚ) - 12) :=
    mul_pos hnm hpoly
  have hden : 0 < (128 : ℚ) * (n : ℚ) := by positivity
  have hneg : -(((n : ℚ) - 1) *
      (79 * (n : ℚ) ^ 2 + 32 * (n : ℚ) - 12)) < 0 := by
    linarith
  exact div_neg_of_neg_of_pos hneg hden

/-- The structured family obeys the claimed positive-integer bound, with the
only equality at the base row `n = 1`. -/
theorem psi_le_rtilde_eq_iff (n : ℕ) (hn : 0 < n) :
    psi n ≤ rtilde n ∧ (psi n = rtilde n ↔ n = 1) := by
  constructor
  · by_cases h1 : n = 1
    · subst n
      norm_num [psi, rtilde]
    · have hn2 : 2 ≤ n := by omega
      exact (sub_neg.mp (psi_sub_rtilde_negative n hn2)).le
  · constructor
    · intro heq
      by_contra hne
      have hn2 : 2 ≤ n := by omega
      have hlt := psi_sub_rtilde_negative n hn2
      have hzero : psi n - rtilde n = 0 := sub_eq_zero.mpr heq
      linarith
    · intro h1
      subst n
      norm_num [psi, rtilde]

/-- The reserve is exactly the quadratic reserve minus the prefix area. -/
theorem rtilde_eq_quadratic_minus_prefixArea (n : ℕ) :
    rtilde n = (5 / 2 : ℚ) * (n : ℚ) ^ 2 - prefixArea n := by
  dsimp [rtilde, prefixArea]
  ring

end MathlibPlus.Algebra.Claim50036
