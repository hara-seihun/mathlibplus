import Mathlib.Tactic

namespace MathlibPlus.Combinatorics

/-- The exact arithmetic grade gap in the minimal-star control from claim 28239.
The two grades are the displayed binomial coefficients. -/
theorem minimalStar_p3_excess_grade_gap_claim28239
    (L : ℕ) (hL : 3 ≤ L) :
    Nat.choose (L - 1) 2 - Nat.choose (L - 2) 2 = L - 2 ∧
      0 < L - 2 := by
  have hsub : L - 1 = (L - 2) + 1 := by omega
  rw [hsub, Nat.choose_succ_succ']
  change Nat.choose (L - 2) 1 + Nat.choose (L - 2) 2 -
      Nat.choose (L - 2) 2 = L - 2 ∧ 0 < L - 2
  rw [Nat.choose_one_right]
  omega

end MathlibPlus.Combinatorics
