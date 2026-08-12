import MathlibPlus.Analysis.ReciprocalXi

open MeasureTheory

namespace MathlibPlus.Open.Analysis.CompletedThetaShellConstruction

/-- Claim 15142.  The packet's translation law fixes the Fourier convention
as the unnormalised kernel `exp (-i * u * x)`, rather than Mathlib's
`2 * π`-normalised real Fourier integral.  The completed xi used here is the
existing pole-removed definition in `MathlibPlus.Analysis.ReciprocalXi`. -/
def completedThetaShellConstruction : Prop :=
  let f : ℕ → ℝ → ℝ := fun n u ↦
    Real.exp (u / 2) * Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u))
  let phi : ℕ → ℝ → ℝ := fun n u ↦
    iteratedDeriv 2 (f n) u - (1 / 4 : ℝ) * f n u
  let Phi : ℝ → ℝ := fun u ↦ ∑' n : ℕ, phi (n + 1) u
  ∀ x : ℝ,
    (∫ u : ℝ,
      Complex.exp (-Complex.I * ((u * x : ℝ) : ℂ)) * (Phi u : ℂ)) =
      MathlibPlus.Analysis.ReciprocalXi.xi
        ((1 / 2 : ℂ) + (x : ℂ) * Complex.I)

end MathlibPlus.Open.Analysis.CompletedThetaShellConstruction
