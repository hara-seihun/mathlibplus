import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis.Claim9444

noncomputable section

/-- A positive shifted logarithmic-derivative mixture has its exact
von-Mangoldt Dirichlet series, with nonnegative coefficients. -/
def exactShiftedLogarithmicDerivativeMixture : Prop :=
  ∀ (μ : Measure NNReal),
    IsFiniteMeasure μ →
    ∀ s : ℂ, 1 < s.re →
      let fμ : ℝ → ℝ := fun u =>
        ∫ r : NNReal, Real.exp (-((r : ℝ) * u)) ∂μ
      let Dμ : ℂ → ℂ := fun w =>
        ∫ r : NNReal,
          (-deriv riemannZeta (w + (r : ℂ))) /
            riemannZeta (w + (r : ℂ)) ∂μ
      (Dμ s =
        ∑' n : ℕ,
          if 2 ≤ n then
            (ArithmeticFunction.vonMangoldt n : ℂ) *
                Complex.exp (-s * Complex.log (n : ℂ)) *
              (fμ (Real.log (n : ℝ)) : ℂ)
          else 0) ∧
      (∀ n : ℕ,
        0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) *
          fμ (Real.log (n : ℝ)))

end

end MathlibPlus.Open.Analysis.Claim9444
