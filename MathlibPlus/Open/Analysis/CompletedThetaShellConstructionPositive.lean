import MathlibPlus.Analysis.ReciprocalXi

open MeasureTheory

namespace MathlibPlus.Open.Analysis.CompletedThetaShellConstructionPositive

/-- Claim 15142.  O-0266 uses the positive-phase Fourier convention
`F₊ f x = ∫ exp (i * u * x) f u du`; the completed xi is the existing
pole-removed definition in `MathlibPlus.Analysis.ReciprocalXi`. -/
def completedThetaShellConstructionPositive : Prop :=
  let f : ℕ → ℝ → ℝ := fun n u ↦
    Real.exp (u / 2) * Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u))
  let phi : ℕ → ℝ → ℝ := fun n u ↦
    iteratedDeriv 2 (f n) u - (1 / 4 : ℝ) * f n u
  let Phi : ℝ → ℝ := fun u ↦ ∑' n : ℕ, phi (n + 1) u
  ∀ x : ℝ,
    (∫ u : ℝ,
      Complex.exp (Complex.I * ((u * x : ℝ) : ℂ)) * (Phi u : ℂ)) =
      MathlibPlus.Analysis.ReciprocalXi.xi
        ((1 / 2 : ℂ) + (x : ℂ) * Complex.I)

end MathlibPlus.Open.Analysis.CompletedThetaShellConstructionPositive
