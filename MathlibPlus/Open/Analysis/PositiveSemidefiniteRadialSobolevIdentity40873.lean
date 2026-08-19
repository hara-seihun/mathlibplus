import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Claim 40873: the radial energy is the positive semidefinite squared norm
of the complex current, with the displayed expanded real integrand. -/
def positiveSemidefiniteRadialSobolevIdentity_claim40873 : Prop :=
  ∀ (a b : ℝ) (Q : ℝ → ℂ) (k : ℕ),
    a ≤ b →
    2 ≤ k →
    ContDiff ℝ 1 Q →
    let Hk : ℝ → ℂ := fun u =>
      Q u ^ (k - 2) *
        (Complex.re (deriv Q u * star (Q u)) : ℂ)
    let radial : ℝ → ℝ := fun u => ‖Q u‖ ^ k
    (∫ u in a..b, ‖deriv radial u‖ ^ 2 =
        (k : ℝ) ^ 2 * ∫ u in a..b, ‖Hk u‖ ^ 2) ∧
      (∫ u in a..b, ‖deriv radial u‖ ^ 2 =
        (k : ℝ) ^ 2 *
          ∫ u in a..b,
            ‖Q u‖ ^ (2 * k - 4) *
              (Complex.re (deriv Q u * star (Q u))) ^ 2)

end MathlibPlus.Open.Analysis
