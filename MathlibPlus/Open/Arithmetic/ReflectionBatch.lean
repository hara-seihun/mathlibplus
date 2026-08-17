import Mathlib

namespace MathlibPlus.Open.Arithmetic.ReflectionBatch

private def intervalReflection (ℓ k : ℕ) : ℕ := ℓ - 1 - k

private def splitDegrees (ℓ k : ℕ) : ℕ × ℕ :=
  (k, ℓ - 1 - k)

private def reflectedSplitDegrees (ℓ k : ℕ) : ℕ × ℕ :=
  splitDegrees ℓ (intervalReflection ℓ k)

/-- Claim 17918: in split coordinates, interval reflection exchanges the two
beta--Laguerre particle degrees and leaves their total equal to ℓ - 1. -/
def reflectionExchangeFixedTotalBetaLaguerreDegree_claim17918 : Prop :=
  ∀ (ℓ k : ℕ), k < ℓ →
    reflectedSplitDegrees ℓ k = (splitDegrees ℓ k).swap ∧
      (splitDegrees ℓ k).1 + (splitDegrees ℓ k).2 = ℓ - 1

end MathlibPlus.Open.Arithmetic.ReflectionBatch
