import Mathlib

noncomputable section

open scoped BigOperators Topology
open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.O0326Superoscillation

/-- Claim 15428: a finite complex measure supported in `[-r,0]` has the
stated finite-difference superoscillation lower bound, including the exact
relative-error factor. -/
def claim15428_finiteDifferenceSuperoscillationLowerBound : Prop :=
  ∀ (r L : ℝ) (a : ℂ) (η : ℝ),
    0 < r →
      0 < L →
        a ≠ 0 →
          0 ≤ η →
            η < 1 →
              ∀ (μ : MeasureTheory.ComplexMeasure ℝ),
                MeasureTheory.IsFiniteMeasure μ.variation →
                  μ.variation.support ⊆ Set.Icc (-r) 0 →
                    let B : ℂ → ℂ := fun z =>
                      μ.integral
                        (fun τ : ℝ =>
                          Complex.exp (Complex.I * (τ : ℂ) * z))
                        (ContinuousLinearMap.mul ℝ ℂ)
                    let M_y : ℝ → ℝ := fun y =>
                      ∫ τ : ℝ, Real.exp (-y * τ) ∂μ.variation
                    let h : ℝ := Real.pi / L
                    ∀ (x₀ y : ℝ) (n : ℕ),
                      (∀ j : Fin (n + 1),
                        ‖B
                            (((x₀ + (j : ℝ) * h : ℝ) : ℂ) +
                              Complex.I * (y : ℂ)) -
                            a * (-1 : ℂ) ^ (j : ℕ)‖ ≤
                          η * ‖a‖) →
                        M_y y / ‖a‖ ≥
                          (1 - η) *
                            (2 * L / (Real.pi * r)) ^ n

end MathlibPlus.Open.ResearchFormalization.O0326Superoscillation
