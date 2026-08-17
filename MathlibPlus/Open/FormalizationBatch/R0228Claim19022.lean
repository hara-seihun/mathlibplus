import Mathlib
import MathlibPlus.Algebra.Claim19020EulerLikeFactor

open MeasureTheory

namespace MathlibPlus.Open.FormalizationBatch.R0228Claim19022

private noncomputable def bilateralLaplace
    (μ : Measure ℝ) (z : ℝ) : ℝ :=
  ∫ x : ℝ, Real.exp (z * x) ∂μ

private noncomputable def additiveConvolution
    (μ ν : Measure ℝ) : Measure ℝ :=
  Measure.map (fun p : ℝ × ℝ => p.1 + p.2) (μ.prod ν)

/-- Claim 19022: the exact positive symmetric three-atom measure has the
bilateral Laplace transform `E_{q,ℓ}`, and convolution turns finite products of
such transforms into products of factors. -/
def claim19022_positiveAtomicConvolution : Prop :=
  ∀ (q ℓ : ℝ), 0 < q → q < 1 → 0 < ℓ →
    let E : ℝ → ℝ :=
      MathlibPlus.Algebra.Claim19020.euler_like_factor_claim19020 q ℓ
    let μ : Measure ℝ :=
      ENNReal.ofReal (1 + q ^ 2) • Measure.dirac 0 +
        ENNReal.ofReal q • Measure.dirac ℓ +
        ENNReal.ofReal q • Measure.dirac (-ℓ)
    IsFiniteMeasure μ ∧
      Measure.map Neg.neg μ = μ ∧
      (∀ z : ℝ, bilateralLaplace μ z = E z) ∧
      (∀ (ν₁ ν₂ : Measure ℝ) (F G : ℝ → ℝ),
        IsFiniteMeasure ν₁ → IsFiniteMeasure ν₂ →
        (∀ z : ℝ, Integrable (fun x : ℝ => Real.exp (z * x)) ν₁) →
        (∀ z : ℝ, Integrable (fun x : ℝ => Real.exp (z * x)) ν₂) →
        (∀ z : ℝ, bilateralLaplace ν₁ z = F z) →
        (∀ z : ℝ, bilateralLaplace ν₂ z = G z) →
        ∀ z : ℝ,
          bilateralLaplace (additiveConvolution ν₁ ν₂) z = F z * G z)

end MathlibPlus.Open.FormalizationBatch.R0228Claim19022
