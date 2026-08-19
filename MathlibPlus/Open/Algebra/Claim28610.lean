import Mathlib

namespace MathlibPlus.Open.Algebra

/-- Claim 28610: the midpoint coordinate has the displayed exact difference
whenever its single denominator is nonzero. -/
def midpointCoordinateDifference_claim28610 : Prop :=
  ∀ (f D : ℝ),
    f + D ≠ 0 →
      let Z : ℝ := ((f - D) / (f + D)) ^ 2
      Z - 1 = (-4 : ℝ) * f * D / (f + D) ^ 2

end MathlibPlus.Open.Algebra
