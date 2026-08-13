import MathlibPlus.Open.AnalyticNumberTheory.PrimeSums.FksHistoryAndNormalization
import MathlibPlus.Open.AnalyticNumberTheory.PrimeSums.FksAsymptoticThetaEnvelope

namespace MathlibPlus.AnalyticNumberTheory.PrimeSums

/-- The two FKS theta-envelope registry presentations are definitionally the same
pointwise inequality after the standard theta-sum and exact-decimal rewrites. -/
theorem previouslyPublishedThetaAmplitude_iff_fksAsymptoticThetaEnvelope :
    MathlibPlus.Open.AnalyticNumberTheory.PrimeSums.previouslyPublishedThetaAmplitude ↔
      MathlibPlus.Open.AnalyticNumberTheory.PrimeSums.fksAsymptoticThetaEnvelope := by
  simp only [MathlibPlus.Open.AnalyticNumberTheory.PrimeSums.previouslyPublishedThetaAmplitude,
    MathlibPlus.Open.AnalyticNumberTheory.PrimeSums.fksAsymptoticThetaEnvelope,
    Chebyshev.theta_eq_sum_primesLE, Nat.primesLE_eq_filter_range]
  norm_num

end MathlibPlus.AnalyticNumberTheory.PrimeSums
