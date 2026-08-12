import Mathlib

namespace MathlibPlus.Analysis

/-- Claim 1218: the retained `log (2 * pi)` normalization is an algebraic
rewrite of the same bound; the source's `T ≥ 1` hypothesis is retained even
though the rewrite itself does not use it. -/
theorem retainedLogTwoPiNormalization_claim1218
    (A m T N M C₁ B : ℝ) (hT : 1 ≤ T) :
    let X : ℝ := Real.log A + m * Real.log T
    (|N - M| ≤ C₁ * (X - m * Real.log (2 * Real.pi)) + B * m) →
      |N - M| ≤ C₁ * X + (B - C₁ * Real.log (2 * Real.pi)) * m := by
  dsimp
  intro h
  convert h using 1 <;> ring

end MathlibPlus.Analysis
