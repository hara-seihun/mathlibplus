import Mathlib.Tactic

namespace MathlibPlus.Algebra

open scoped BigOperators

/-!
Claim 11668: powers of a finite sum of pairwise orthogonal idempotent prime
blocks contain no mixed-prime words.  The coefficients are represented by
ring elements commuting with all blocks, which is the scalar-coefficient
reading of the source weights.
-/

/-- Pairwise orthogonal idempotent prime blocks have no mixed terms in powers
of their weighted sum. -/
theorem orthogonalFinitePrimeBlockPowers_claim11668
    {R : Type*} [Semiring R]
    (S : Finset ℕ) (_hS : ∀ p ∈ S, Nat.Prime p)
    (w E : ℕ → R)
    (hidem : ∀ p, p ∈ S → E p * E p = E p)
    (horth : ∀ p, p ∈ S → ∀ q, q ∈ S → p ≠ q → E p * E q = 0)
    (hcomm : ∀ p, p ∈ S → ∀ q, q ∈ S → Commute (w p) (E q))
    (k : ℕ) (hk : 1 ≤ k) :
    (∑ p ∈ S, w p * E p) ^ k =
      ∑ p ∈ S, (w p) ^ k * E p := by
  have hpow : ∀ n : ℕ,
      (∑ p ∈ S, w p * E p) ^ (n + 1) =
        ∑ p ∈ S, (w p) ^ (n + 1) * E p := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        rw [pow_succ, ih]
        simp only [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.sum_eq_single p]
        · have hsame :
              ((w p) ^ (n + 1) * E p) * (w p * E p) =
                (w p) ^ (n + 2) * E p := by
            calc
              ((w p) ^ (n + 1) * E p) * (w p * E p) =
                  (w p) ^ (n + 1) * ((E p * w p) * E p) := by
                    simp [mul_assoc]
              _ = (w p) ^ (n + 1) * ((w p * E p) * E p) := by
                    rw [← (hcomm p hp p hp).eq]
              _ = ((w p) ^ (n + 1) * w p) * (E p * E p) := by
                    simp [mul_assoc]
              _ = ((w p) ^ (n + 1) * w p) * E p := by
                    rw [hidem p hp]
              _ = (w p) ^ (n + 2) * E p := by
                    have hpows :
                        (w p) ^ (n + 1) * w p = (w p) ^ (n + 2) := by
                      simpa [Nat.add_assoc] using
                        (pow_succ (w p) (n + 1)).symm
                    rw [hpows]
          exact hsame
        · intro q hq hqp
          have hzero :
              ((w q) ^ (n + 1) * E q) * (w p * E p) = 0 := by
            calc
              ((w q) ^ (n + 1) * E q) * (w p * E p) =
                  (w q) ^ (n + 1) * ((E q * w p) * E p) := by
                    simp [mul_assoc]
              _ = (w q) ^ (n + 1) * ((w p * E q) * E p) := by
                    rw [← (hcomm p hp q hq).eq]
              _ = ((w q) ^ (n + 1) * w p) * (E q * E p) := by
                    simp [mul_assoc]
              _ = 0 := by
                    rw [horth q hq p hp hqp, mul_zero]
          exact hzero
        · intro hpnot
          exact False.elim (hpnot hp)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simpa [Nat.succ_eq_add_one] using hpow n

end MathlibPlus.Algebra
