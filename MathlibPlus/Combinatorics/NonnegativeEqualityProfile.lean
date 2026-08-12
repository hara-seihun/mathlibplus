import Mathlib

open BigOperators

namespace MathlibPlus.Combinatorics.NonnegativeEqualityProfile

/-- Claim 34822: the nonnegative recurrence profile has the advertised
binomial equality after the missing top term is restored. -/
theorem nonnegativeEqualityProfile (U : ℕ → ℕ) (_hU0 : U 0 = 1)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      (U n = (∑ r ∈ Finset.range n, Nat.choose n r * U r)))
    (n : ℕ) (hn : 1 ≤ n) :
    (∑ r ∈ Finset.range (n + 1), Nat.choose n r * U r) = 2 * U n := by
  rw [Finset.sum_range_succ, hrec n hn]
  simp [two_mul]

end MathlibPlus.Combinatorics.NonnegativeEqualityProfile
