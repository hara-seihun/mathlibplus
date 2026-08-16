import Mathlib

open Filter
open scoped Topology

namespace MathlibPlus.Open.ResearchFormalization.O0326Claim15429

/-- Claim 15429: for the exact finite-complex-measure transform used in Record 11,
an alternating sample block whose physical length is comparable to `S` pays a
logarithmic cancellation cost of order `L * S * log (L / r)` when `r = o(L)`.
The sample approximation and its norm scale are part of the premise. -/
def endpointLocalBlockSuperoscillationCost_claim15429 : Prop :=
  ∀ (L r : ℕ → ℝ) (S : ℝ) (n : ℕ → ℕ)
    (x₀ y : ℕ → ℝ) (a : ℕ → ℂ) (η : ℝ)
    (μ : ℕ → MeasureTheory.ComplexMeasure ℝ),
    Filter.Tendsto L Filter.atTop Filter.atTop →
    (∀ k, 0 < L k) →
    0 < S →
    Filter.Tendsto (fun k => r k / L k) Filter.atTop (𝓝 0) →
    (∀ᶠ k in Filter.atTop, 0 < r k) →
    (∀ᶠ k in Filter.atTop, a k ≠ 0) →
    0 ≤ η →
    η < 1 →
    (∀ᶠ k in Filter.atTop,
      MeasureTheory.IsFiniteMeasure (μ k).variation ∧
        (μ k).variation.support ⊆ Set.Icc (-r k) 0) →
    (∀ᶠ k in Filter.atTop, 2 * L k / (Real.pi * r k) > 1) →
    (∃ cLower cUpper : ℝ,
      0 < cLower ∧ 0 < cUpper ∧
        (∀ᶠ k in Filter.atTop,
          cLower * L k * S / Real.pi ≤ (n k : ℝ)) ∧
        (∀ᶠ k in Filter.atTop,
          (n k : ℝ) ≤ cUpper * L k * S / Real.pi)) →
    let B : ℕ → ℂ → ℂ := fun k z =>
      (μ k).integral
        (fun τ : ℝ => Complex.exp (Complex.I * (τ : ℂ) * z))
        (ContinuousLinearMap.mul ℝ ℂ)
    let M : ℕ → ℝ → ℝ := fun k yy =>
      ∫ τ : ℝ, Real.exp (-yy * τ) ∂(μ k).variation
    (∀ᶠ k in Filter.atTop,
      ∀ j : Fin (n k + 1),
        ‖B k
            ((((x₀ k + (j : ℝ) * Real.pi / L k : ℝ) : ℂ) +
              Complex.I * (y k : ℂ))) -
            a k * (-1 : ℂ) ^ (j : ℕ)‖ ≤
          η * ‖a k‖) →
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ k in Filter.atTop,
        c * L k * S * Real.log (L k / r k) ≤
          Real.log (M k (y k) / ‖a k‖)

end MathlibPlus.Open.ResearchFormalization.O0326Claim15429
