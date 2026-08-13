import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim28725

/-!
Claim 28725 identifies the displayed `P3` excess with `2 * binom 5 2`.
The packet does not define the associated tree or Schur quotient, so this file
formalizes the exact numerical evaluation rather than silently supplying those
source-specific carriers.
-/

/-- The displayed `(5,5,2)` excess arithmetic evaluates to twenty. -/
theorem p3ExcessArithmetic : 2 * Nat.choose 5 2 = 20 := by
  norm_num [Nat.choose]

end MathlibPlus.Combinatorics.Claim28725
