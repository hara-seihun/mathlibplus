import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.NR2

noncomputable section

/-- Claim 15554: the prime logarithms have a divergent Cayley radial-defect
sum.  The natural-number series is zero-extended away from the exact carrier
of primes at least three. -/
def primeLogBlaschkeDivergence_claim15554 : Prop :=
  let cayley : ℂ → ℂ := fun z => (z - 1) / (z + 1)
  let term : ℕ → ℝ := fun p =>
    1 - ‖cayley (Real.log (p : ℝ) : ℂ)‖
  (∀ p : ℕ, Nat.Prime p → 3 ≤ p →
      term p = 2 / (Real.log (p : ℝ) + 1)) ∧
    ¬ Summable (fun p : ℕ =>
      if Nat.Prime p ∧ 3 ≤ p then term p else 0)

end

end MathlibPlus.Open.Analysis.NR2
