import Mathlib

/-!
# The c-dial counterfeit family

This file fixes explicit conventions for the real source, its unnormalized complex Fourier
transform, and the whole-line integral representation of the modified Bessel function used in
the packet's transform formula.
-/

namespace MathlibPlus.Analysis.CDialCounterfeit

/-- The real `c`-dial source from the counterfeit family. -/
noncomputable def source (c t : ℝ) : ℝ :=
  (4 * Real.pi ^ 2 * Real.cosh (9 * t / 2) -
      6 * Real.pi * c * Real.cosh (5 * t / 2)) *
    Real.exp (-2 * Real.pi * Real.cosh (2 * t))

/-- The unnormalized complex Fourier transform convention used for the `c`-dial formula. -/
noncomputable def fourierTransform (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, (f t : ℂ) * Complex.exp (Complex.I * z * (t : ℂ))

/-- The standard whole-line integral representation of the modified Bessel function `K_ν(β)`. -/
noncomputable def modifiedBesselK (ν β : ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    ∫ x : ℝ, Complex.exp (-β * Complex.cosh (x : ℂ) + ν * (x : ℂ))

/-- The claimed explicit Bessel expression for the Fourier transform of `source c`. -/
noncomputable def transformExpression (c : ℝ) (z : ℂ) : ℂ :=
  2 * (Real.pi : ℂ) ^ 2 *
      (modifiedBesselK ((Complex.I * z + 9 / 2) / 2) (2 * Real.pi) +
        modifiedBesselK ((Complex.I * z - 9 / 2) / 2) (2 * Real.pi)) -
    3 * Real.pi * c *
      (modifiedBesselK ((Complex.I * z + 5 / 2) / 2) (2 * Real.pi) +
        modifiedBesselK ((Complex.I * z - 5 / 2) / 2) (2 * Real.pi))

end MathlibPlus.Analysis.CDialCounterfeit
