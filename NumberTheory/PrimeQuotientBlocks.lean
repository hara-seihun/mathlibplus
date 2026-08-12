import Mathlib

open scoped BigOperators

namespace MathlibPlus.NumberTheory.PrimeQuotientBlocks

/-- Once the positive quotient block is known to be a singleton, its two
weights reduce to the displayed totient and reciprocal-square values. -/
theorem weights_of_singleton_claim13374 {N q : ℕ}
    (hblock :
      (Finset.Icc 1 N).filter (fun r => N / r = N / q) = {q}) :
    (∑ r ∈ (Finset.Icc 1 N).filter (fun r => N / r = N / q),
        (Nat.totient r : ℝ) / (r : ℝ)) =
        (Nat.totient q : ℝ) / (q : ℝ) ∧
      (∑ r ∈ (Finset.Icc 1 N).filter (fun r => N / r = N / q),
        (1 - 1 / (r : ℝ) ^ 2)) =
        1 - 1 / (q : ℝ) ^ 2 := by
  constructor
  · rw [hblock]
    simp
  · rw [hblock]
    simp

/-- The prime totient specialization in claim 13374. -/
theorem totient_prime_ratio_claim13374 {q : ℕ} (hq : Nat.Prime q) :
    (Nat.totient q : ℝ) / (q : ℝ) = 1 - 1 / (q : ℝ) := by
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast hq.ne_zero
  rw [Nat.totient_prime hq]
  have hq1 : 1 ≤ q := hq.one_le
  rw [Nat.cast_sub hq1]
  field_simp [hq0]
  ring_nf

end MathlibPlus.NumberTheory.PrimeQuotientBlocks
