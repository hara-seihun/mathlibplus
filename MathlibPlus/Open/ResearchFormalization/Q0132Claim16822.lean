import MathlibPlus.Open.ResearchFormalization.Q0132Claim16817

namespace MathlibPlus.Open.ResearchFormalization.Q0132Claim16822

open MathlibPlus.Open.ResearchFormalization.Q0132Claim16817

noncomputable section

/-- The six reindexed witness inequalities `τ(n-k) ≤ k+2`, for the exact
    shifts `1 ≤ k ≤ 6` in the strict-prefix range. -/
def firstSixWitnessInequalities (n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ 6 → k < n →
    tau (n - k) ≤ k + 2

/-- Claim 16822: for a strictly larger-than-24 candidate, the first six
    witness inequalities already force the stated divisibility and primality. -/
def firstSixShiftsReduction_claim16822 : Prop :=
  ∀ n : ℕ, 24 < n →
    firstSixWitnessInequalities n →
      210 ∣ n ∧ Nat.Prime ((n - 6) / 6)

end

end MathlibPlus.Open.ResearchFormalization.Q0132Claim16822
