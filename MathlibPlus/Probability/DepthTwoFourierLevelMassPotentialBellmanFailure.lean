-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import MathlibPlus.Open.Probability.DepthTwoFourierLevelMassPotentialBellmanFailure

namespace MathlibPlus.Probability

/-- Kernel-check the explicit finite Fourier/Bellman obstruction. -/
theorem depthTwoFourierLevelMassPotentialBellmanFailure_proved :
    MathlibPlus.Open.Probability.depthTwoFourierLevelMassPotentialBellmanFailure := by
  unfold MathlibPlus.Open.Probability.depthTwoFourierLevelMassPotentialBellmanFailure
  native_decide

end MathlibPlus.Probability
