import Mathlib

namespace MathlibPlus.Combinatorics.Claim37875

/-- If a residual term has order `n - d*J`, positivity of `d*J` makes
that order strictly smaller than `n`; term existence is represented by the
necessary bound `d*J ≤ n`. -/
theorem residualOrderStrict
    (n d J : ℕ) (hterm : d * J ≤ n) (hpositive : 0 < d * J) :
    n - d * J < n := by
  omega

end MathlibPlus.Combinatorics.Claim37875
