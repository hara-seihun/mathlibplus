import MathlibPlus.Open.Analysis.CauchyFourierMaxIdentity
import MathlibPlus.Open.AnalyticNumberTheory.PrimeSums.CauchyKernelIntegral

namespace MathlibPlus.Analysis

noncomputable section

/-- The two Cauchy-kernel Fourier integral formulations are definitionally the
same identity after expanding their local abbreviations and normalizing the
commuting complex factors. -/
theorem cauchyFourierMaxIdentity_iff_exactCauchyKernelIntegral :
    MathlibPlus.Open.Analysis.cauchyFourierMaxIdentity ↔
      MathlibPlus.Open.AnalyticNumberTheory.PrimeSums.exactCauchyKernelIntegral := by
  constructor
  · intro h m n hm hn
    dsimp [MathlibPlus.Open.Analysis.cauchyFourierMaxIdentity] at h
    dsimp [MathlibPlus.Open.AnalyticNumberTheory.PrimeSums.exactCauchyKernelIntegral]
    simpa [mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using
      h m n hm hn
  · intro h m n hm hn
    dsimp [MathlibPlus.Open.AnalyticNumberTheory.PrimeSums.exactCauchyKernelIntegral] at h
    dsimp [MathlibPlus.Open.Analysis.cauchyFourierMaxIdentity]
    simpa [mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using
      h m n hm hn

end
end MathlibPlus.Analysis
