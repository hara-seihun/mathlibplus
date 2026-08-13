import MathlibPlus.Open.Probability.DepthTwoFourierLevelMassPotentialBellmanFailure

namespace MathlibPlus.Probability

/-- Kernel-check the explicit finite Fourier/Bellman obstruction. -/
theorem depthTwoFourierLevelMassPotentialBellmanFailure_proved :
    MathlibPlus.Open.Probability.depthTwoFourierLevelMassPotentialBellmanFailure := by
  unfold MathlibPlus.Open.Probability.depthTwoFourierLevelMassPotentialBellmanFailure
  native_decide

end MathlibPlus.Probability
