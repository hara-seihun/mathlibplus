import MathlibPlus.Open.Analysis.PrimeCountingRepairs

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

noncomputable section

open MathlibPlus.Open.Analysis

/-- Claim 978: the exact sharp-coefficient non-strict bound on every
published audit row, including equality at and only at its listed optimizer. -/
def exactBestNonStrictDenominatorBound_claim978 : Prop :=
  ∀ r ∈ auditRows, ∀ x : ℝ, (r.start : ℝ) ≤ x →
    primeCountingReal x ≤
        x / (Real.log x - sharpCoefficient r) ∧
      (primeCountingReal x =
          x / (Real.log x - sharpCoefficient r) ↔
        x = (r.optimizer : ℝ))

end

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
