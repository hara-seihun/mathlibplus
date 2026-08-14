import Mathlib

namespace MathlibPlus.Open.Analysis.Superoscillation

/-- Endpoint-supported Fourier--Laplace transforms pay exponentially for an
alternating run of samples. -/
def exponentialEndpointDepthSuperoscillationCost : Prop :=
  ∀ (r L : ℝ) (a : ℂ) (η : ℝ),
    0 < r →
    r < L →
    a ≠ 0 →
    0 ≤ η →
    η < 1 →
    ∀ (μ : MeasureTheory.ComplexMeasure ℝ),
      MeasureTheory.IsFiniteMeasure μ.variation →
      μ.variation.support ⊆ Set.Icc (-r) 0 →
      let B : ℂ → ℂ := fun z =>
        μ.integral
          (fun τ : ℝ => Complex.exp (Complex.I * (τ : ℂ) * z))
          (ContinuousLinearMap.mul ℝ ℂ)
      let M : ℝ → ℝ := fun y =>
        ∫ τ : ℝ, Real.exp (-y * τ) ∂μ.variation
      ∀ (x₀ y : ℝ) (n : ℕ),
        (∀ j : Fin (n + 1),
          ‖B (((x₀ + (j : ℝ) * Real.pi / L : ℝ) : ℂ) +
              Complex.I * (y : ℂ)) -
              a * (-1 : ℂ) ^ (j : ℕ)‖ ≤ η * ‖a‖) →
        M y / ‖a‖ ≥ (1 - η) * (2 * L / (Real.pi * r)) ^ n

end MathlibPlus.Open.Analysis.Superoscillation
