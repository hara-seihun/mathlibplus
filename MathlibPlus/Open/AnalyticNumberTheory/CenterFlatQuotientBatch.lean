import Mathlib

open scoped BigOperators Topology
open Filter MeasureTheory

namespace MathlibPlus.Open.AnalyticNumberTheory.CenterFlatQuotientBatch

noncomputable section

/-- Claim 15482: the quartic arithmetic multiplier has an algebraic tail and
cannot obey either exact exponentially decaying arithmetic law. -/
def claim15482 : Prop :=
  ∀ R : ℝ, R ≠ 0 →
    let qR : ℂ → ℂ := fun s =>
      1 + (s - (1 / 2 : ℂ)) ^ 4 / (R : ℂ) ^ 4
    let qLogDerivative : ℂ → ℂ := fun s =>
      -deriv qR s / qR s
    let strictPositiveGapLaplace : (ℂ → ℂ) → Prop := fun h =>
      ∃ (δ σ₀ : ℝ) (μ : Measure ℝ),
        0 < δ ∧
        μ (Set.Iio δ) = 0 ∧
        (∀ σ : ℝ, σ₀ < σ →
          Integrable (fun t : ℝ => Real.exp (-σ * t)) μ) ∧
        (∀ s : ℂ, σ₀ < s.re →
          h s = ∫ t : ℝ, Complex.exp (-s * (t : ℂ)) ∂μ)
    let ordinaryDirichletNoFirstTerm : (ℂ → ℂ) → Prop := fun h =>
      ∃ (a : {n : ℕ // 2 ≤ n} → ℂ) (σ₀ : ℝ),
        (∀ σ : ℝ, σ₀ < σ →
          Summable (fun n =>
            ‖a n‖ * Real.exp (-σ * Real.log (n.1 : ℝ)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          h s = ∑' n, a n *
            Complex.exp (-s * (Real.log (n.1 : ℝ) : ℂ)))
    (∀ s : ℂ, qR s ≠ 0 →
      qLogDerivative s =
        -4 * (s - (1 / 2 : ℂ)) ^ 3 /
          ((R : ℂ) ^ 4 + (s - (1 / 2 : ℂ)) ^ 4)) ∧
    Tendsto (fun x : ℝ => (x : ℂ) * qLogDerivative (x : ℂ)) atTop
      (𝓝 (-4 : ℂ)) ∧
    ¬ strictPositiveGapLaplace qLogDerivative ∧
    ¬ ordinaryDirichletNoFirstTerm qLogDerivative

end

end MathlibPlus.Open.AnalyticNumberTheory.CenterFlatQuotientBatch
