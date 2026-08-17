import MathlibPlus.Open.Analysis.ThetaHeatClaim19067
import MathlibPlus.Open.Analysis.ThetaCoefficientFlowClaim19070

open MeasureTheory
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.Claim19069

open MathlibPlus.Open.Analysis.Claim19067
open MathlibPlus.Open.Analysis.Claim19070

noncomputable section

/-- Claim 19069: evenness makes the square-variable transform single-valued
and entire, with both displayed coefficient expansions and positive gamma
coefficients. -/
def squareVariableCoefficientFormula_claim19069 : Prop :=
  ∀ t : ℝ,
    Function.Even (literalHeatTransform t) ∧
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
          (∀ k : ℕ, 0 < literalGamma t k)

end

end MathlibPlus.Open.Analysis.Claim19069
