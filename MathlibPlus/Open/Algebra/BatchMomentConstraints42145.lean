import Mathlib

namespace MathlibPlus.Open.Algebra

open scoped BigOperators
noncomputable section

/-- The elementary coefficient obtained by summing products over `k`-subsets. -/
def elementaryCoeff {n : ℕ} (x : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ s : Finset (Fin n), if s.card = k then (∏ i ∈ s, x i) else 0

/-- The `k`-th power sum of a finite list of real roots. -/
def powerSum {n : ℕ} (x : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i : Fin n, x i ^ k

/-- Claim 42145: positive roots force the consecutive Maclaurin inequalities and
power-sum log-convexity.  The quantifiers record exactly the range in which the
consecutive coefficients and the three moments are available. -/
def maclaurinAndPowerSumLogConvexity_claim42145 : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ),
    (∀ i, 0 < x i) →
      (∀ k : ℕ, 1 ≤ k → k < n →
        Real.rpow
            (elementaryCoeff x k / (Nat.choose n k : ℝ))
            (1 / (k : ℝ)) ≥
          Real.rpow
            (elementaryCoeff x (k + 1) / (Nat.choose n (k + 1) : ℝ))
            (1 / ((k + 1 : ℕ) : ℝ))) ∧
      (∀ k : ℕ, 2 ≤ k →
        powerSum x k * powerSum x (k - 2) ≥ powerSum x (k - 1) ^ 2)

end
end MathlibPlus.Open.Algebra
