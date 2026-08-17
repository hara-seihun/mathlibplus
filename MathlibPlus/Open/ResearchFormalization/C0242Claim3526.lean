import Mathlib

noncomputable section

open MeasureTheory Set

namespace MathlibPlus.Open.ResearchFormalization.C0242

/-- Claim 3526: a finite complex measure supported in the endpoint interval
carries the Fourier--Laplace field and its weighted total-variation reserve.
The displayed functions are explicit arguments constrained by their exact
integral formulas, rather than unconstrained transform callbacks. -/
def claim3526_endpointLocalFourierLaplaceTransform
    (r : ℝ) (μ : ComplexMeasure ℝ) (B : ℂ → ℂ) (M : ℝ → ℝ) : Prop :=
  IsFiniteMeasure μ.variation ∧
    μ.variation.support ⊆ Icc (-r) 0 ∧
      (∀ z : ℂ,
        B z =
          μ.integral
            (fun τ : ℝ => Complex.exp (Complex.I * (τ : ℂ) * z))
            (ContinuousLinearMap.mul ℝ ℂ)) ∧
        (∀ y : ℝ,
          M y = ∫ τ : ℝ, Real.exp (-y * τ) ∂μ.variation)

end MathlibPlus.Open.ResearchFormalization.C0242
