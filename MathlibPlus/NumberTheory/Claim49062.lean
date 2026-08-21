import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace MathlibPlus.NumberTheory.Claim49062

theorem add_one_le_two_pow_claim49062_aux (a : ℕ) : a + 1 ≤ 2 ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
      calc
        a.succ + 1 = (a + 1) + 1 := by omega
        _ ≤ 2 ^ a + 2 ^ a :=
          Nat.add_le_add ih (Nat.one_le_pow _ _ (by decide))
        _ = 2 ^ a.succ := by rw [Nat.pow_succ, mul_comm, two_mul]

/-- The exact divisor-count inequality from claim 49062, expressed through
Mathlib's divisor-count and prime-factorization APIs. -/
theorem divisor_card_le_two_pow_factorization_claim49062 {m : ℕ} (hm : m ≠ 0) :
    m.divisors.card ≤ 2 ^ (∑ p ∈ m.primeFactors, m.factorization p) := by
  rw [Nat.card_divisors hm]
  calc
    ∏ p ∈ m.primeFactors, (m.factorization p + 1)
        ≤ ∏ p ∈ m.primeFactors, 2 ^ (m.factorization p) := by
          apply Finset.prod_le_prod'
          intro p hp
          exact add_one_le_two_pow_claim49062_aux _
    _ = 2 ^ (∑ p ∈ m.primeFactors, m.factorization p) := by
          exact Finset.prod_pow_eq_pow_sum _ _ _

/-- The logarithmic sufficient condition in claim 49062.  The displayed
hypothesis is precisely `Omega(n-k) ≤ beta * log(k+2)` with
`beta = 1 / log 2`; the strict shift hypotheses ensure that `n-k` is positive. -/
theorem divisor_card_le_shift_of_log_budget_claim49062
    {n k : ℕ} (hk : 1 < k) (hkn : k < n)
    (hOmega :
      ((∑ p ∈ (n - k).primeFactors, (n - k).factorization p : ℕ) : ℝ)
        ≤ Real.log (k + 2) / Real.log 2) :
    (n - k).divisors.card ≤ k + 2 := by
  have hm : n - k ≠ 0 := Nat.sub_ne_zero_of_lt hkn
  let omega : ℕ := ∑ p ∈ (n - k).primeFactors, (n - k).factorization p
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hmul : (omega : ℝ) * Real.log 2 ≤ Real.log (k + 2) := by
    exact (le_div_iff₀ hlog2).mp hOmega
  have hlogpow : Real.log ((2 : ℝ) ^ omega) ≤ Real.log (k + 2) := by
    rw [Real.log_pow]
    exact hmul
  have hpow_real : (2 : ℝ) ^ omega ≤ (k + 2 : ℕ) := by
    have hpow_pos : (2 : ℝ) ^ omega ∈ Set.Ioi (0 : ℝ) := by
      show 0 < (2 : ℝ) ^ omega
      exact pow_pos (by norm_num) _
    have hk_pos : ((k + 2 : ℕ) : ℝ) ∈ Set.Ioi (0 : ℝ) := by
      change 0 < ((k + 2 : ℕ) : ℝ)
      exact_mod_cast (show 0 < k + 2 by omega)
    apply (Real.strictMonoOn_log.le_iff_le hpow_pos hk_pos).mp
    simpa using hlogpow
  have hpow_nat : 2 ^ omega ≤ k + 2 := by
    exact_mod_cast hpow_real
  have hcard : (n - k).divisors.card ≤ 2 ^ omega := by
    dsimp [omega]
    exact divisor_card_le_two_pow_factorization_claim49062 hm
  exact hcard.trans hpow_nat

end MathlibPlus.NumberTheory.Claim49062
