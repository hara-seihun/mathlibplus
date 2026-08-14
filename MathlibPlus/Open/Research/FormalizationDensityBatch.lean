import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch

def shiftedFiniteDepthDensity (a b M t : ℝ) : ℝ :=
  Real.exp (-(a + 1 / 4) * t) * (2 * M + 4 * Real.cos (b * t))

def shiftedFiniteDepthDerivativeBound : Prop :=
  ∀ (a b M : ℝ) (k : ℕ) (t : ℝ),
    let c : ℝ := a + 1 / 4
    let g : ℝ → ℝ := shiftedFiniteDepthDensity a b M
    ((-1 : ℝ) ^ k * iteratedDeriv k g t =
        Real.exp (-c * t) *
          (2 * M * c ^ k +
            4 * Complex.re
              (((c : ℂ) - Complex.I * (b : ℂ)) ^ k *
                Complex.exp (Complex.I * (b * t : ℂ)))) ∧
      (-1 : ℝ) ^ k * iteratedDeriv k g t ≥
        Real.exp (-c * t) *
          (2 * M * c ^ k -
            4 * Real.rpow (c ^ 2 + b ^ 2) ((k : ℝ) / 2)))

end MathlibPlus.Open.ResearchFormalizationBatch
