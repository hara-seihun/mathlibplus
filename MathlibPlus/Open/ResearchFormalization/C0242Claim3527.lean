import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.C0242

noncomputable section

/-- Iterated forward differences with the convention
`Δ_h f z = f (z+h) - f z`. -/
def iteratedForwardDifference_claim3527
    (h : ℝ) (B : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0, z => B z
  | n + 1, z =>
      iteratedForwardDifference_claim3527 h B n (z + (h : ℂ)) -
        iteratedForwardDifference_claim3527 h B n z

/--
Claim 3527: for the finite complex measure and endpoint-supported
Fourier--Laplace carrier, the order-`n` forward difference at every complex
point is the displayed multiplier integral, with `h = π / L`.
-/
def exactIteratedForwardDifferenceIdentity_claim3527 : Prop :=
  ∀ (r : ℝ) (μ : MeasureTheory.ComplexMeasure ℝ) (B : ℂ → ℂ),
    MeasureTheory.IsFiniteMeasure μ.variation →
    μ.variation.support ⊆ Set.Icc (-r) 0 →
    (∀ z : ℂ,
      B z =
        μ.integral
          (fun τ : ℝ =>
            Complex.exp (Complex.I * (τ : ℂ) * z))
          (ContinuousLinearMap.mul ℝ ℂ)) →
    ∀ (L : ℝ) (n : ℕ) (x₀ y : ℝ),
      let h : ℝ := Real.pi / L
      iteratedForwardDifference_claim3527 h B n
          ((x₀ : ℂ) + Complex.I * (y : ℂ)) =
        μ.integral
          (fun τ : ℝ =>
            Complex.exp
                (Complex.I * (τ : ℂ) *
                  ((x₀ : ℂ) + Complex.I * (y : ℂ))) *
              (Complex.exp
                  (Complex.I * (τ : ℂ) * (h : ℂ)) - 1) ^ n)
          (ContinuousLinearMap.mul ℝ ℂ)

end

end MathlibPlus.Open.ResearchFormalization.C0242
