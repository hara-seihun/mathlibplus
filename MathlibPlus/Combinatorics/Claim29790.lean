import Mathlib

namespace MathlibPlus.Combinatorics

/-- Claim 29790: the P3-excess grade of a double-star core with pendant
valencies `p` and `q` is the displayed sum of binomial coefficients. -/
def doubleStarP3ExcessGrade_claim29790 (p q : ℕ) : ℕ :=
  Nat.choose p 2 + Nat.choose q 2

end MathlibPlus.Combinatorics
