import MathlibPlus.Open.Analysis.HarmonicLogDivisor

namespace MathlibPlus.Open.ResearchFormalization.R4192HarmonicLowerBound

open scoped BigOperators
open MathlibPlus.Analysis.HarmonicLogDivisor

noncomputable section

/-- The pre-query stage variance from the beta--Bernoulli output-only model. -/
def stageVariance53203 (n m : ℕ) : ℝ :=
  2 * ((n : ℝ) + 2) * ((n : ℝ) - (m : ℝ)) /
    (3 * (n : ℝ) ^ 2 * ((m : ℝ) + 2))

/-- The complete-block output-only area, summed over the pre-query stages. -/
def completeBlockArea53203 (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range n, stageVariance53203 n m

/-- The harmonic lower-bound sum retained from the first `r` stages. -/
def harmonicRestriction53203 (n : ℕ) : ℝ :=
  let r := n / 2
  (1 / 3 : ℝ) *
    (∑ m ∈ Finset.range r, (1 : ℝ) / ((m : ℝ) + 2))

/-- Claim 53203: for `r=floor(n/2)`, the first `r` pre-query stages give the
stated harmonic lower bound, which is unbounded and rules out a universal
constant bound for the complete-block output-only area. -/
def claim53203 : Prop :=
  (∀ n : ℕ, 1 ≤ n →
    completeBlockArea53203 n ≥ harmonicRestriction53203 n ∧
      harmonicRestriction53203 n =
        (H (n / 2 + 1) - 1) / 3) ∧
  (∀ C : ℝ, ∃ n : ℕ, 1 ≤ n ∧ C < completeBlockArea53203 n) ∧
  ¬ (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → completeBlockArea53203 n ≤ C)

end
end MathlibPlus.Open.ResearchFormalization.R4192HarmonicLowerBound
