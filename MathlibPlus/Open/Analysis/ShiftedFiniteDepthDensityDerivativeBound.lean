import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable def shiftedFiniteDepthDensityDerivativeBound : Prop :=
  ∀ (a M b t : ℝ) (k : ℕ),
    let c : ℝ := a + 1 / 4
    let g : ℝ → ℝ := fun t => Real.exp (-c * t) *
      (2 * M + 4 * Real.cos (b * t))
    (-1 : ℝ) ^ k * iteratedDeriv k g t =
        Real.exp (-c * t) *
          (2 * M * c ^ k +
            4 * Complex.re
              (((c : ℂ) - Complex.I * (b : ℂ)) ^ k *
                Complex.exp (Complex.I * ((b * t : ℝ) : ℂ)))) ∧
      (-1 : ℝ) ^ k * iteratedDeriv k g t ≥
        Real.exp (-c * t) *
          (2 * M * c ^ k -
            4 * Real.rpow (c ^ 2 + b ^ 2) ((k : ℝ) / 2))

end MathlibPlus.Open.Analysis
