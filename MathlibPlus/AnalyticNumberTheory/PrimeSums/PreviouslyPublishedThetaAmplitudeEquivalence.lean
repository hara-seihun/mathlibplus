import MathlibPlus.Open.AnalyticNumberTheory.PrimeSums.FksHistoryAndNormalization
import MathlibPlus.Open.AnalyticNumberTheory.PrimeSums.FksAsymptoticThetaEnvelope

namespace MathlibPlus.AnalyticNumberTheory.PrimeSums

/-- The previously published theta envelope and the FKS presentation are the
same proposition after expanding the finite prime sum and exact decimals. -/
theorem previouslyPublishedThetaAmplitude_iff_fksAsymptoticThetaEnvelope :
    MathlibPlus.Open.AnalyticNumberTheory.PrimeSums.previouslyPublishedThetaAmplitude ↔
      MathlibPlus.Open.AnalyticNumberTheory.PrimeSums.fksAsymptoticThetaEnvelope := by
  dsimp [MathlibPlus.Open.AnalyticNumberTheory.PrimeSums.previouslyPublishedThetaAmplitude,
    MathlibPlus.Open.AnalyticNumberTheory.PrimeSums.fksAsymptoticThetaEnvelope]
  constructor
  · intro h x hx
    have hx' := h x hx
    rw [Chebyshev.theta_eq_sum_primesLE, Nat.primesLE_eq_filter_range] at hx'
    convert hx' using 1; norm_num
  · intro h x hx
    have hx' := h x hx
    rw [Chebyshev.theta_eq_sum_primesLE, Nat.primesLE_eq_filter_range]
    convert hx' using 1; norm_num

end MathlibPlus.AnalyticNumberTheory.PrimeSums
