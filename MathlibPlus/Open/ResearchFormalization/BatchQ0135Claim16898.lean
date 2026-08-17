import MathlibPlus.Open.ResearchFormalization.BatchQ0135

namespace MathlibPlus.Open.ResearchFormalization.BatchQ0135

/-- The one-sided epsilon formulation of the reported `(1+o(1)) n/log n`
asymptotic upper bound for the exact prime-power upper bound. -/
def upperBoundAsymptotic : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → composite n →
      (n : ℝ) / (largestPrimePowerComponent n : ℝ) ≤
        (1 + ε) * (n : ℝ) / Real.log (n : ℝ)

/-- Claim 16898: the elementary lower and exact-prime-power upper bounds,
with the stated asymptotic interpretation of the upper bound. -/
def claim16898 : Prop :=
  (∀ n : ℕ, composite n →
    leastPrimeFactor n ≤ rowBinomialGcd n ∧
      rowBinomialGcd n ≤ n / largestPrimePowerComponent n) ∧
    upperBoundAsymptotic

end MathlibPlus.Open.ResearchFormalization.BatchQ0135
