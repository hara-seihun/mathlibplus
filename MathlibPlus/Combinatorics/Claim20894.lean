import Mathlib

namespace MathlibPlus.Combinatorics

/-- The exact natural-number base-size consequence in claim 20894:
`N ≤ d + a` and `a < d` force `d ≥ ⌊N/2⌋ + 1`. -/
theorem baseSizeConsequence_claim20894 {N d a : ℕ}
    (hN : N ≤ d + a) (ha : a < d) :
    N / 2 + 1 ≤ d := by
  omega

end MathlibPlus.Combinatorics
