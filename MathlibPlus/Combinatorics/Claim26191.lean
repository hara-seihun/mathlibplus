import Mathlib.RingTheory.Binomial
import Mathlib.Tactic

namespace MathlibPlus.Combinatorics

/-- The generalized-binomial Vandermonde expansion with the host and card
edge counts represented by natural cardinalities. -/
theorem vandermondeEdgeDeficit_claim26191 (eG eH s : ℕ) :
    Ring.choose ((eG : ℚ) - (eH : ℚ)) s =
      ∑ j ∈ Finset.range (s + 1),
        Ring.choose (eG : ℚ) j * Ring.choose (-(eH : ℚ)) (s - j) := by
  rw [sub_eq_add_neg, Ring.add_choose_eq s
    (Commute.all (eG : ℚ) (-(eH : ℚ)))]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => Ring.choose (eG : ℚ) i * Ring.choose (-(eH : ℚ)) j) s]

end MathlibPlus.Combinatorics
