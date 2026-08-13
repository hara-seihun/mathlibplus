import Mathlib

namespace MathlibPlus.NumberTheory.Claim20166

/-- Two selected primes from `(R / 2, R]` have product larger than `P * R`
when `R > 4 * P`.  The interval is written without natural-number division as
`R < 2 * p`. -/
theorem selectedPrimeProduct_gt (P R p q : ℕ)
    (hRP : 4 * P < R)
    (_hp : p.Prime) (_hq : q.Prime)
    (hp : R < 2 * p) (hq : R < 2 * q) :
    P * R < p * q := by
  nlinarith

/-- Consequently, no positive index at most `P * R` can be divisible by two
distinct selected primes.  The source-specific coefficient `Q` is represented
by the explicit positive index and support bound in the hypotheses. -/
theorem noTwoSelectedPrimeDivisors
    (P R n : ℕ) (hRP : 4 * P < R) (hn : 0 < n) (hnPR : n ≤ P * R) :
    ¬ (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧
      R < 2 * p ∧ R < 2 * q ∧ p ≤ R ∧ q ≤ R ∧ p ∣ n ∧ q ∣ n) := by
  rintro ⟨p, q, hp, hq, hpq, hpl, hql, hpu, hqu, hpdiv, hqdiv⟩
  have hpqdiv : p * q ∣ n := hp.dvd_mul_of_dvd_ne hpq hq hpdiv hqdiv
  have hpq_le : p * q ≤ n := Nat.le_of_dvd hn hpqdiv
  have hprod : P * R < p * q := selectedPrimeProduct_gt P R p q hRP hp hq hpl hql
  omega

end MathlibPlus.NumberTheory.Claim20166
