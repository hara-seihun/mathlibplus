import Mathlib

namespace MathlibPlus.Algebra.Claim21266

/-- Claim 21266, with the range variable represented by an integer so that
`floor (n/2) - 1` is not silently changed into truncated natural subtraction.
The hypotheses are exactly the displayed range `0 ≤ q ≤ floor(n/2)-1`. -/
theorem positiveDiagonalCoefficient (n : ℕ) (q : ℤ)
    (hq0 : 0 ≤ q)
    (hq : q ≤ (n / 2 : ℕ) - 1) :
    ((n : ℤ) - 1 - 2 * q) * ((Nat.factorial (n - 2) : ℕ) : ℤ) > 0 := by
  have hn : 2 ≤ n := by omega
  have hfloor : 2 * (n / 2) ≤ n := by omega
  have hcoeff : 0 < (n : ℤ) - 1 - 2 * q := by
    omega
  have hfact : 0 < ((Nat.factorial (n - 2) : ℕ) : ℤ) := by
    exact_mod_cast (Nat.factorial_pos (n - 2))
  exact mul_pos hcoeff hfact

end MathlibPlus.Algebra.Claim21266
