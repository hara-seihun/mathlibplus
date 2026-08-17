import Mathlib
import MathlibPlus.Open.Analysis.SignedCarrierSplit

namespace MathlibPlus.Open.ResearchFormalization.SignedResidualOperators

open MathlibPlus.Open.FormalizationBatch

noncomputable section

/-- Claim 6031: on the real-interval carrier, the two signed residual
operators and the carrier baseline are the displayed expressions. -/
def claim6031_signedResidualOperators : Prop :=
  ∀ (I : Set ℝ) (A T : ℝ → ℂ),
    Set.OrdConnected I ∧
      (∀ x : ℝ, x ∈ I → A x ≠ 0) ∧
      ContDiff ℝ 2 A ∧
      ContDiff ℝ 2 T →
    let a : ℝ → ℂ := carrierLogDerivative A
    let b : ℝ → ℂ := carrierSecondCoefficient A
    let ω : ℝ → ℂ := carrierPhase A
    let p : ℝ → ℝ := carrierImaginaryDerivative A
    let c : ℝ → ℝ := carrierCurvature A
    let P₀T : ℝ → ℂ := carrierPZero A T
    let P₁T : ℝ → ℂ := carrierPOne A T
    let B_A : ℝ → ℝ := carrierBaseline A
    ∀ x : ℝ, x ∈ I →
      P₀T x =
          -deriv (deriv T) x -
            4 * Complex.I * (p x : ℂ) * deriv T x +
            2 * (c x : ℂ) * T x ∧
        P₁T x = -deriv (deriv T) x - 2 * b x * T x ∧
        B_A x = c x - (ω x ^ 2 * b x).re

end
end MathlibPlus.Open.ResearchFormalization.SignedResidualOperators
