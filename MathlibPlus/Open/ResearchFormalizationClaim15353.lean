import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalizationClaim15353

noncomputable section

/-- The reciprocal-density assertion for the explicit O-0321 counterfeit. -/
def claim15353 : Prop :=
  let y : ℝ → ℝ := fun t =>
    (1 / 4 : ℝ) * (1 + t ^ 2) ^ 3 * (t ^ 4 + 4) *
      Real.cosh (Real.pi * t / 2)
  let reciprocal : ℝ → ℂ := fun t => ((y t)⁻¹ : ℂ)
  let sechFactor : ℝ → ℂ := fun t =>
    ((Real.cosh (Real.pi * t / 2))⁻¹ : ℂ)
  let rationalFactor : ℝ → ℂ := fun t =>
    ((4 / ((1 + t ^ 2) ^ 3 * (t ^ 4 + 4)) : ℝ) : ℂ)
  let sechDensity : ℝ → ℝ := fun x =>
    (Real.cosh x)⁻¹ / Real.pi
  let fourierKernel : ℝ → ℝ → ℂ := fun t x =>
    Complex.exp (Complex.I * ((t * x : ℝ) : ℂ))
  let densityFourier : (ℝ → ℝ) → ℝ → ℂ := fun p t =>
    ∫ x : ℝ, fourierKernel t x * (p x : ℂ) ∂volume
  let characteristicIntegral : Measure ℝ → ℝ → ℂ := fun μ t =>
    ∫ x : ℝ, fourierKernel t x ∂μ
  let isCharacteristicFunction : (ℝ → ℂ) → Prop := fun f =>
    ∃ μ : Measure ℝ,
      μ Set.univ = 1 ∧ ∀ t : ℝ, f t = characteristicIntegral μ t
  let convolutionDensity : Measure ℝ → ℝ → ℝ := fun μ x =>
    ∫ y : ℝ, sechDensity (x - y) ∂μ
  (∀ x : ℝ, 0 < sechDensity x) ∧
    Integrable sechDensity volume ∧
    (∫ x : ℝ, sechDensity x ∂volume) = 1 ∧
    (∀ t : ℝ, sechFactor t = densityFourier sechDensity t) ∧
    isCharacteristicFunction sechFactor ∧
    (∃ μ : Measure ℝ,
      μ Set.univ = 1 ∧
        (∀ t : ℝ, reciprocal t = sechFactor t * characteristicIntegral μ t) ∧
        (∀ t : ℝ, rationalFactor t = characteristicIntegral μ t) ∧
        (∀ x : ℝ, 0 < convolutionDensity μ x) ∧
        Integrable (convolutionDensity μ) volume ∧
        (∫ x : ℝ, convolutionDensity μ x ∂volume) = 1 ∧
        (∀ t : ℝ,
          reciprocal t =
            ∫ x : ℝ, fourierKernel t x * (convolutionDensity μ x : ℂ) ∂volume)) ∧
    (∀ t : ℝ, reciprocal t = sechFactor t * rationalFactor t) ∧
    Integrable reciprocal volume

end
end MathlibPlus.Open.ResearchFormalizationClaim15353
