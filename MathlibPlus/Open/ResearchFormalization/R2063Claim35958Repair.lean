import MathlibPlus.Open.ResearchFormalization.R2063Claim35959

open scoped BigOperators
open Filter

namespace MathlibPlus.Open.ResearchFormalization.R2063Claim35958Repair

open MathlibPlus.Open.NumberTheory.Claim35956
open MathlibPlus.Open.ResearchFormalization.R2063Claim35959

noncomputable section

/-- The logarithmic mass of the exact small-nonzero-remainder carrier. -/
def smallRemainderLogMass (N : ℕ) : ℝ :=
  ∑ p ∈ smallRemainderPrimes N, Real.log (p : ℝ)

/-- The interval logarithm occurring in the divisor bound. -/
def smallRemainderIntervalLogSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (smallRemainderCutoff N),
    Real.log ((N - k : ℕ) : ℝ)

/-- Claim 35958: small nonzero remainders are supported by the short interval
of predecessors, and their logarithmic mass is negligible at the critical
primorial scale. -/
def claim35958_smallRemainderPrimesNegligible : Prop :=
  (∀ᶠ N : ℕ in atTop,
    smallRemainderCutoff N ≤ N ∧
      (∀ p ∈ smallRemainderPrimes N,
        ∃ k ∈ Finset.Icc 1 (smallRemainderCutoff N), p ∣ N - k) ∧
      smallRemainderLogMass N ≤ smallRemainderIntervalLogSum N ∧
      smallRemainderIntervalLogSum N ≤
        (smallRemainderCutoff N : ℝ) * Real.log (N : ℝ)) ∧
  Asymptotics.IsLittleO atTop
    (fun N : ℕ =>
      (smallRemainderCutoff N : ℝ) * Real.log (N : ℝ))
    (fun N : ℕ => criticalScale N) ∧
  Asymptotics.IsLittleO atTop smallRemainderLogMass
    (fun N : ℕ => criticalScale N)

end

end MathlibPlus.Open.ResearchFormalization.R2063Claim35958Repair
