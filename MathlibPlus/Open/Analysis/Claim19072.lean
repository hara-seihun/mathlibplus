import Mathlib
import MathlibPlus.Open.Analysis.ThetaHeatClaim19067
import MathlibPlus.Open.Analysis.SquareVariableThetaClaim19069
import MathlibPlus.Open.Analysis.VerticalShiftExact

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis.Claim19072

noncomputable section

open MathlibPlus.Open.Analysis.Claim19067
open MathlibPlus.Open.Analysis.Claim19069
open MathlibPlus.Open.Analysis.Claim19070
open MathlibPlus.Open.Analysis.VerticalShiftExact

private def negativeRealZeroLocation (F : ℂ → ℂ) : Prop :=
  ∀ w : ℂ, F w = 0 → w.im = 0 ∧ w.re < 0

/-- Claim 19072: with the literal square-variable carrier and its positive
coefficients, the negative-real zero condition for Θ is exactly the real-zero
condition for H under Θ(-(z²)/4)=H(z). -/
def squareVariableZeroLocationEquivalence : Prop :=
  ∀ t : ℝ,
    ∃ Θ : ℂ → ℂ,
      Differentiable ℂ Θ ∧
        (∀ w : ℂ,
          Θ w = literalHeatTransform t
            ((2 : ℂ) * Complex.I * Complex.sqrt w)) ∧
        (∀ z : ℂ,
          Θ (-(z ^ 2) / (4 : ℂ)) = literalHeatTransform t z) ∧
        (∀ w : ℂ,
          Θ w = ∑' k : ℕ,
            (((4 : ℝ) ^ k * literalMoment t (2 * k) /
              (Nat.factorial (2 * k) : ℝ) : ℝ) : ℂ) * w ^ k) ∧
        (∀ w : ℂ,
          Θ w = ∑' k : ℕ,
            (literalGamma t k : ℂ) * w ^ k /
              (Nat.factorial k : ℂ)) ∧
        (∀ k : ℕ, 0 < literalGamma t k) ∧
        (negativeRealZeroLocation Θ ↔
          realRootedFunction (literalHeatTransform t))

end

end MathlibPlus.Open.Analysis.Claim19072
