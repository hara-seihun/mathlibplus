import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.NewResearch2.R0209

noncomputable section

private def symmetricTwoPointLaw18837 (a : ℝ) : Measure ℝ :=
  (1 / 2 : ENNReal) • Measure.dirac a +
    (1 / 2 : ENNReal) • Measure.dirac (-a)

private def evenLaw18837 (μ : Measure ℝ) : Prop :=
  μ Set.univ = 1 ∧
    ∀ s : Set ℝ, MeasurableSet s →
      μ s = μ ((fun u : ℝ => -u) ⁻¹' s)

private def convexEvenLawClass18837 (C : Set (Measure ℝ)) : Prop :=
  (∀ μ : Measure ℝ, μ ∈ C → evenLaw18837 μ) ∧
    (∀ (μ₁ μ₂ : Measure ℝ), μ₁ ∈ C → μ₂ ∈ C →
      ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
        ENNReal.ofReal p • μ₁ + ENNReal.ofReal (1 - p) • μ₂ ∈ C)

private def qTwoPointDefect18837
    (q : ℕ → Measure ℝ → ℝ) (a b p : ℝ) : Prop :=
  let ρ : ℝ → Measure ℝ := symmetricTwoPointLaw18837
  let μₚ : Measure ℝ :=
    ENNReal.ofReal p • ρ a + ENNReal.ofReal (1 - p) • ρ b
  q 2 μₚ - p * q 2 (ρ a) - (1 - p) * q 2 (ρ b) =
      -(p * (1 - p) / 4) * (a ^ 2 - b ^ 2) ^ 2 ∧
    -(p * (1 - p) / 4) * (a ^ 2 - b ^ 2) ^ 2 < 0

private def fixedPositiveKernel18837 (K : ℝ → Measure ℝ) : Prop :=
  (∀ u : ℝ, K u Set.univ = 1) ∧
    (∀ s : Set ℝ, MeasurableSet s →
      Measurable (fun u : ℝ ↦ K u s))

private def fixedPositiveKernelRepresentation18837
    (C : Set (Measure ℝ)) (q : ℕ → Measure ℝ → ℝ) : Prop :=
  ∃ K : ℝ → Measure ℝ,
    fixedPositiveKernel18837 K ∧
      ∀ (μ : Measure ℝ), μ ∈ C →
        ∀ k : ℕ,
          ∫ t : ℝ, t ^ k ∂(Measure.bind μ K) = q (k + 1) μ

/-- Claim 18837: the exact q₂ non-affinity defect on the two symmetric
point-mass laws rules out every fixed positive Markov kernel on the stated
convex even-law class. -/
def claim18837_noFixedPositiveKernelForShiftedQMoments : Prop :=
  ∀ (q : ℕ → Measure ℝ → ℝ) (C : Set (Measure ℝ)),
    convexEvenLawClass18837 C →
      ∀ (a b p : ℝ), a ^ 2 ≠ b ^ 2 → 0 < p → p < 1 →
        symmetricTwoPointLaw18837 a ∈ C →
        symmetricTwoPointLaw18837 b ∈ C →
        qTwoPointDefect18837 q a b p →
          ¬ fixedPositiveKernelRepresentation18837 C q

end

end MathlibPlus.Open.NewResearch2.R0209
