import Mathlib

namespace MathlibPlus.Analysis

/-- Claim 15376: an even function differentiable at the origin and convex on
`[0, ∞)` lies above its origin tangent, which is the origin value. -/
def evenDifferentiableConvexOnIciOriginLe : Prop :=
  ∀ (f : ℝ → ℝ),
    DifferentiableAt ℝ f 0 →
    Function.Even f →
    ConvexOn ℝ (Set.Ici (0 : ℝ)) f →
    ∀ (y : ℝ), 0 ≤ y →
      f y ≥ f 0 + deriv f 0 * y ∧ f 0 + deriv f 0 * y = f 0

end MathlibPlus.Analysis
