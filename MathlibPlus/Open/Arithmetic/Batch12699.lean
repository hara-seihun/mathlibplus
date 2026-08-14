import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Arithmetic

/-
For the coefficient of degree k, factors of degree greater than k and powers
of (F - 1) greater than k cannot contribute.  Thus these finite expressions
are the exact degree-k presentation of the formal product and logarithm in
Claim 12699, without requiring an infinite-product topology on PowerSeries.
-/
noncomputable def partitionProductUpTo (k : ℕ) : PowerSeries ℚ :=
  ∏ r ∈ Finset.range (k + 1), (1 - PowerSeries.X ^ (r + 1))⁻¹

noncomputable def formalLogUpTo (k : ℕ) (F : PowerSeries ℚ) : PowerSeries ℚ :=
  ∑ m ∈ Finset.range (k + 1),
    (((-1 : ℚ) ^ (m + 1)) / (m : ℚ)) • (F - 1) ^ m

def sigmaOne (k : ℕ) : ℚ :=
  ∑ d ∈ k.divisors, (d : ℚ)

/-- Claim 12699: the logarithmic coefficient is the divisor sum divided by k. -/
def claim12699_divisorSumLogCoefficient : Prop :=
  ∀ k : ℕ, 0 < k →
    PowerSeries.coeff k (formalLogUpTo k (partitionProductUpTo k)) =
      sigmaOne k / (k : ℚ)

end MathlibPlus.Open.Arithmetic
