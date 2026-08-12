import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

open scoped BigOperators

namespace MathlibPlus.Open.NumberTheory

/-
Statement-fidelity note for claim 9723: the source writes `sigma(n)/n` and
`v_p(n)` with the positive integer domain implicit.  This node makes that
domain explicit (`0 < n`) and uses `ArithmeticFunction.sigma 1` for the
ordinary divisor sum sigma function.
-/

/-- Claim 9723: the local divisor-factor quotient after multiplying by a prime. -/
def localDivisorFactorQuotient_claim9723 : Prop :=
  ∀ (p n : ℕ), Nat.Prime p → 0 < n →
    let a := padicValNat p n
    (((ArithmeticFunction.sigma 1) (n * p) : ℝ) / (n * p)) /
        (((ArithmeticFunction.sigma 1) n : ℝ) / n) =
      1 + 1 / (∑ j ∈ Finset.Icc 1 (a + 1), (p : ℝ) ^ j)

end MathlibPlus.Open.NumberTheory
