import Mathlib

namespace MathlibPlus.Combinatorics

private lemma chooseRatio_desc_bound (n k : ℕ) (hk : k ≤ n) :
    5 ^ k * (3 * n / 5).descFactorial k ≤
      3 ^ k * n.descFactorial k := by
  have hd : 5 * (3 * n / 5) ≤ 3 * n := by
    exact Nat.mul_div_le (3 * n) 5
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
      have hk' : k ≤ n := by omega
      have hfac : 5 * ((3 * n / 5) - k) ≤ 3 * (n - k) := by
        omega
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
      calc
        5 ^ k * 5 * ((3 * n / 5 - k) * (3 * n / 5).descFactorial k) =
            (5 ^ k * (3 * n / 5).descFactorial k) *
              (5 * (3 * n / 5 - k)) := by ring
        _ ≤ (3 ^ k * n.descFactorial k) * (3 * (n - k)) :=
          Nat.mul_le_mul (ih n hk' hd) hfac
        _ = 3 ^ k * 3 * ((n - k) * n.descFactorial k) := by ring

/-- Claim 35800: with `d_n = floor (3n/5)`, the hypergeometric ratio is at
most `(3/5)^k`.  The natural-number convention `Nat.choose d k = 0` when
`k > d` implements the source's zero-ratio convention. -/
theorem chooseRatio_floorThreeFifths (n k : ℕ) (hk : k ≤ n) :
    ((Nat.choose (3 * n / 5) k : ℝ) / Nat.choose n k) ≤
      ((3 : ℝ) / 5) ^ k := by
  have hnat := chooseRatio_desc_bound n k hk
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose] at hnat
  have hnat' :
      5 ^ k * Nat.choose (3 * n / 5) k ≤ 3 ^ k * Nat.choose n k := by
    apply Nat.le_of_mul_le_mul_left (c := Nat.factorial k) _
      (Nat.factorial_pos k)
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hnat
  have hcross :
      (5 : ℝ) ^ k * (Nat.choose (3 * n / 5) k : ℝ) ≤
        (3 : ℝ) ^ k * Nat.choose n k := by
    exact_mod_cast hnat'
  have hchoosepos : 0 < (Nat.choose n k : ℝ) := by
    exact_mod_cast Nat.choose_pos hk
  apply (div_le_iff₀ hchoosepos).2
  rw [div_pow]
  calc
    (Nat.choose (3 * n / 5) k : ℝ) ≤
        ((3 : ℝ) ^ k * Nat.choose n k) / (5 : ℝ) ^ k := by
      apply (le_div_iff₀ (by positivity : 0 < (5 : ℝ) ^ k)).2
      simpa [mul_comm, mul_left_comm, mul_assoc] using hcross
    _ = (3 : ℝ) ^ k / (5 : ℝ) ^ k * Nat.choose n k := by ring

end MathlibPlus.Combinatorics
