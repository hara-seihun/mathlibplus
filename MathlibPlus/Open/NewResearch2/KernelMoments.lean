import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.NewResearch2.R0209

/-- Claim 18835: moments produced by one fixed positive Markov kernel are
affine in the input law. -/
def claim18835_markovKernelMomentsAffine : Prop :=
  ∀ (K : ℝ → Measure ℝ),
    (∀ u : ℝ, K u Set.univ = 1) →
    (∀ s : Set ℝ, MeasurableSet s → Measurable (fun u : ℝ ↦ K u s)) →
    (∀ (μ : Measure ℝ) (k : ℕ),
      ∫ t : ℝ, t ^ k ∂(Measure.bind μ K) =
        ∫ u : ℝ, (∫ t : ℝ, t ^ k ∂(K u)) ∂μ) ∧
    (∀ (μ₁ μ₂ μₚ : Measure ℝ) (p : ℝ), 0 ≤ p → p ≤ 1 →
      (∀ s : Set ℝ, MeasurableSet s →
        μₚ s = ENNReal.ofReal p * μ₁ s +
          ENNReal.ofReal (1 - p) * μ₂ s) →
      ∀ k : ℕ,
        ∫ t : ℝ, t ^ k ∂(Measure.bind μₚ K) =
          p * (∫ t : ℝ, t ^ k ∂(Measure.bind μ₁ K)) +
            (1 - p) * (∫ t : ℝ, t ^ k ∂(Measure.bind μ₂ K)))

end MathlibPlus.Open.NewResearch2.R0209
