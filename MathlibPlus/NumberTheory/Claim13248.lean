import Mathlib

namespace MathlibPlus.NumberTheory.Claim13248

/-- Claim 13248: explicit cyclotomic prime-power family for powers of three. -/
theorem primePowerCyclotomicFamily (k : ℕ) (hk : 1 ≤ k) :
    Polynomial.cyclotomic (3 ^ k) ℤ =
        Polynomial.X ^ (2 * 3 ^ (k - 1)) +
          Polynomial.X ^ (3 ^ (k - 1)) + 1 ∧
      (Polynomial.cyclotomic (3 ^ k) ℤ).natDegree = 2 * 3 ^ (k - 1) := by
  have hp : Nat.Prime 3 := by norm_num
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  constructor
  · rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum hp]
    have hpow : ((Polynomial.X : Polynomial ℤ) ^ 3 ^ n) ^ 2 =
        ((Polynomial.X : Polynomial ℤ) ^ 2) ^ 3 ^ n := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    simp [Finset.sum_range_succ, hpow, pow_mul]
    ring
  · rw [Polynomial.natDegree_cyclotomic]
    rw [Nat.totient_prime_pow hp (Nat.succ_pos n)]
    exact Nat.mul_comm _ _

end MathlibPlus.NumberTheory.Claim13248
