import MathlibPlus.Open.Analysis.LocalKernelAsymptotic

namespace MathlibPlus.Open.ResearchFormalization.Claim9203

open MathlibPlus.Open

/-- Claim 9203: along the relevant prime arguments, the positive threshold
has the simplified center with the stated logarithmic remainder. -/
def claim9203_simplifiedThresholdCenter : Prop :=
  isBigOAlongPrimes
    (fun q : ℕ =>
      thetaThreshold q -
        ((q : ℝ) - (Real.log (q : ℝ) + 1) / 2 +
          1 / (2 * (Real.log (q : ℝ) + 1))))
    (fun q : ℕ =>
      (Real.log (q : ℝ)) ^ 2 / (q : ℝ))

end MathlibPlus.Open.ResearchFormalization.Claim9203
