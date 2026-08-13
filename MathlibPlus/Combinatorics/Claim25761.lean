import Mathlib

open scoped BigOperators

namespace MathlibPlus.Combinatorics

/-- The generalized-binomial Vandermonde expansion used for edge deficits. -/
theorem vandermondeEdgeDeficit_claim25761 (eG eH : ℤ) (s : ℕ) :
    Ring.choose (eG - eH) s =
      ∑ j ∈ Finset.range (s + 1),
        Ring.choose eG j * Ring.choose (-eH) (s - j) := by
  rw [show eG - eH = eG + -eH by ring,
    Ring.add_choose_eq s (Commute.all eG (-eH))]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

end MathlibPlus.Combinatorics
