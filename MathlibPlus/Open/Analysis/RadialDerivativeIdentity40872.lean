import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Claim 40872: the radial derivative identity holds at every point, including
zeros of the complex carrier, without a quotient by that carrier. -/
def radialDerivativeIdentity_claim40872 : Prop :=
  ∀ (Q : ℝ → ℂ) (k : ℕ),
    2 ≤ k →
    ContDiff ℝ 1 Q →
    ∀ u : ℝ,
      HasDerivAt (fun t : ℝ => ‖Q t‖ ^ k)
        ((k : ℝ) * ‖Q u‖ ^ (k - 2) *
          Complex.re (deriv Q u * star (Q u))) u

end MathlibPlus.Open.Analysis
