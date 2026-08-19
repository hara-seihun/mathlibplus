import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchC0084

/-- The finite divisor-lattice exponential packet used for `Δ_k(y)`. -/
noncomputable def divisorDelta (k : ℕ) (y : ℝ) : ℝ :=
  ∑ d ∈ k.divisors,
    (ArithmeticFunction.moebius d : ℝ) * Real.exp (-(y * (d : ℝ)))

/-- Claim 8330: the divisor packet has the exact boundary value zero for
indices above one, while its index-one boundary value is one. -/
def claim8330_divisorLatticeBoundaryZero : Prop :=
  (∀ k : ℕ, 1 < k →
    divisorDelta k 0 =
      ∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℝ) ∧
      (∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℝ)) = 0) ∧
    divisorDelta 1 0 = 1

end MathlibPlus.Open.ResearchFormalization.BatchC0084
