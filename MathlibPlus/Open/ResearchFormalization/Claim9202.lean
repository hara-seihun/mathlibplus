import MathlibPlus.Open.Analysis.LocalKernelAsymptotic

namespace MathlibPlus.Open.ResearchFormalization.Claim9202

open MathlibPlus.Open

/-- Claim 9202: the full threshold expansion, with the remainder interpreted by
`isBigOAlongPrimes` on the canonical positive threshold carrier. -/
def claim9202_fullThresholdExpansion : Prop :=
  isBigOAlongPrimes
    (fun q : ℕ =>
      thetaThreshold q -
        ((q : ℝ) -
          Real.log (q : ℝ) * (Real.log (q : ℝ) + 2) /
            (2 * (Real.log (q : ℝ) + 1)) +
          Real.log (q : ℝ) ^ 3 *
            (2 * Real.log (q : ℝ) ^ 2 +
              7 * Real.log (q : ℝ) + 8) /
            (24 * (Real.log (q : ℝ) + 1) ^ 3 * (q : ℝ)) +
          Real.log (q : ℝ) ^ 4 * (Real.log (q : ℝ) + 2) *
            (2 * Real.log (q : ℝ) ^ 2 +
              5 * Real.log (q : ℝ) + 6) /
            (48 * (Real.log (q : ℝ) + 1) ^ 5 * (q : ℝ) ^ 2)))
    (fun q : ℕ =>
      Real.log (q : ℝ) ^ 3 / (q : ℝ) ^ 3)

end MathlibPlus.Open.ResearchFormalization.Claim9202
