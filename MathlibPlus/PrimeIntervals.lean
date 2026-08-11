import Mathlib

/-!
# Consecutive-power interval containment

This file formalizes the exact algebraic bridge in Record 13 of legacy packet
`C-0085`. It does not assert the packet's analytic theta-increment estimate or the
existence of primes in the resulting interval.
-/

namespace MathlibPlus.PrimeIntervals

/-- The first two terms after `n ^ 69` in the binomial expansion already imply
that the explicit-formula window lies strictly inside the consecutive-power gap. -/
theorem binomialContainment69 (n : ℕ) (_hn : 1 ≤ n) :
    n ^ 69 + 69 * n ^ 68 < (n + 1) ^ 69 := by
  rw [add_pow]
  let s : Finset ℕ := {68, 69}
  have hsubset : s ⊆ Finset.range (69 + 1) := by
    intro k hk
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> norm_num
  have hzero_mem : 0 ∈ Finset.range (69 + 1) := by norm_num
  have hzero_not_mem : 0 ∉ s := by norm_num [s]
  have hzero_pos :
      0 < n ^ 0 * 1 ^ (69 - 0) * Nat.choose 69 0 := by norm_num
  have hlt := Finset.sum_lt_sum_of_subset
    (f := fun m => n ^ m * 1 ^ (69 - m) * Nat.choose 69 m)
    hsubset hzero_mem hzero_not_mem hzero_pos (fun _ _ _ => Nat.zero_le _)
  norm_num [s] at hlt ⊢
  simpa [Nat.add_comm, Nat.mul_comm] using hlt

/-- Consequently, every prime in the packet's half-open explicit-formula window is
strictly below the next consecutive `69`th power. -/
theorem primeInExplicitWindow_lt_nextPower (n p : ℕ) (hn : 1 ≤ n)
    (_hp : Nat.Prime p) (_hlower : n ^ 69 < p)
    (hupper : p ≤ n ^ 69 + 69 * n ^ 68) :
    p < (n + 1) ^ 69 :=
  lt_of_le_of_lt hupper (binomialContainment69 n hn)

end MathlibPlus.PrimeIntervals
