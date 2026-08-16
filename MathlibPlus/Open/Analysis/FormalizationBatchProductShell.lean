import Mathlib

namespace MathlibPlus.Open.Analysis.FormalizationBatchProductShell

/-- The shell scale occurring in the theta primitive. -/
noncomputable def thetaShellX (n : ℕ) (t : ℝ) :=
  Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * t)

/-- The primitive theta sum, with the summation range `n ≥ 1` made explicit. -/
noncomputable def thetaPrimitive (t : ℝ) : ℝ :=
  Real.exp (t / 2) * ∑' n : ℕ, if 0 < n then Real.exp (-(thetaShellX n t)) else 0

/-- The Fourier kernel with the frequency convention used by the claims. -/
noncomputable def thetaFourierKernel (ξ d : ℝ) : ℂ :=
  Complex.exp (Complex.I * (ξ : ℂ) * (d : ℂ))

/-- The nonnegative density in the Wigner realization. -/
noncomputable def thetaDensity (u d : ℝ) : ℝ :=
  thetaPrimitive (u / 2 + d) * thetaPrimitive (u / 2 - d)

/-- The Wigner realization of `h_x(u)` supplied by the admitted primitive identity. -/
noncomputable def thetaH (x u : ℝ) : ℂ :=
  ∫ d : ℝ, (thetaDensity u d : ℂ) * thetaFourierKernel (2 * x) d

/-- The finite-matrix positivity condition for a complex-valued function on `ℝ`. -/
def positiveDefiniteRealComplex (f : ℝ → ℂ) : Prop :=
  ∀ n : ℕ, ∀ z : Fin n → ℝ, ∀ c : Fin n → ℂ,
    (∑ i, ∑ j, star (c i) * c j * f (z i - z j)).im = 0 ∧
      0 ≤ (∑ i, ∑ j, star (c i) * c j * f (z i - z j)).re

/-- Positive-definiteness and continuity of the theta Wigner realization. -/
def claim_13705 : Prop :=
  ∀ u : ℝ,
    Continuous (fun x : ℝ => thetaH x u) ∧
      positiveDefiniteRealComplex (fun x : ℝ => thetaH x u) ∧
      (∀ d : ℝ, 0 ≤ thetaDensity u d) ∧
      (∀ x : ℝ,
        thetaH x u =
          ∫ d : ℝ, (thetaDensity u d : ℂ) * thetaFourierKernel (2 * x) d)

end MathlibPlus.Open.Analysis.FormalizationBatchProductShell
