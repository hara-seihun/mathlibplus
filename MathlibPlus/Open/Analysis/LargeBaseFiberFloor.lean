import Mathlib

open scoped BigOperators ENNReal Topology
open Filter MeasureTheory

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- The density used for the critical Cauchy boundary measure. -/
def criticalCauchyDensity (t : ℝ) : ℝ :=
  1 / (2 * Real.pi * ((1 : ℝ) / 4 + t ^ 2))

/-- The critical Cauchy measure associated with `criticalCauchyDensity`. -/
def criticalCauchyMeasure : Measure ℝ :=
  Measure.withDensity volume (fun t => ENNReal.ofReal (criticalCauchyDensity t))

/-- The disk coordinate corresponding to `s = 1/2 + it`. -/
def criticalCoordinate (t : ℝ) : ℂ :=
  1 - 1 / ((1 / 2 : ℂ) + Complex.I * (t : ℂ))

/-- The residual base `Z(z) = z ζ(1/(1-z))` on the critical line. -/
def criticalResidual (t : ℝ) : ℂ :=
  criticalCoordinate t *
    riemannZeta (1 / (1 - criticalCoordinate t))

/-- The large-base parameter `r = q^(-1/2)`. -/
def largeBase (q : ℕ) : ℝ :=
  Real.rpow (q : ℝ) (-(1 / 2 : ℝ))

/-- The singular inner function from the admitted disk-coordinate statement. -/
def singularInner (q : ℕ) (z : ℂ) : ℂ :=
  Complex.exp
    (-((Real.log (q : ℝ) : ℂ) / 2) * ((1 + z) / (1 - z)))

/-- The period `T_q = 2π/log q`. -/
def fiberPeriod (q : ℕ) : ℝ :=
  2 * Real.pi / Real.log (q : ℝ)

/-- The normalized residual base `H_q` on the disk. -/
def normalizedResidual (q : ℕ) (z : ℂ) : ℂ :=
  (z * riemannZeta (1 / (1 - z))) *
    (1 - (largeBase q : ℂ) * singularInner q z) /
      (1 - (largeBase q : ℂ) ^ 2)

/-- The critical-line boundary function associated with `H_q`. -/
def criticalBase (q : ℕ) (t : ℝ) : ℂ :=
  normalizedResidual q (criticalCoordinate t)

/-- The fiber sum `D_q`. -/
def fiberD (q : ℕ) (x : ℝ) : ℝ :=
  ∑' k : ℤ,
    criticalCauchyDensity (x + (k : ℝ) * fiberPeriod q)

/-- The fiber sum `C_q`. -/
def fiberC (q : ℕ) (x : ℝ) : ℂ :=
  ∑' k : ℤ,
    (criticalCauchyDensity (x + (k : ℝ) * fiberPeriod q) : ℂ) *
      star (criticalBase q (x + (k : ℝ) * fiberPeriod q))

/-- The fiber sum `A_q`. -/
def fiberA (q : ℕ) (x : ℝ) : ℝ :=
  ∑' k : ℤ,
    criticalCauchyDensity (x + (k : ℝ) * fiberPeriod q) *
      ‖criticalBase q (x + (k : ℝ) * fiberPeriod q)‖ ^ 2

/-- The exact fiberwise least-squares quantity `δ_q`. -/
def fiberFloor (q : ℕ) : ℝ :=
  ∫ x in Set.Ioc 0 (fiberPeriod q),
    fiberD q x - ‖fiberC q x‖ ^ 2 / fiberA q x

/-- Uniform convergence in the real-valued fiber shift. -/
def uniformlyReal (f : ℕ → ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ q in atTop, ∀ x : ℝ, |f q x - a| < ε

/-- Uniform convergence in the complex-valued fiber shift. -/
def uniformlyComplex (f : ℕ → ℝ → ℂ) (a : ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ q in atTop, ∀ x : ℝ, ‖f q x - a‖ < ε

/--
The large-base fiber-floor limit claim.  The `eLpNorm` limit is convergence of
`H_q` to `Z` in the critical Cauchy `H²`, and the three epsilon statements
are the uniform shifted-lattice limits for `D_q`, `C_q`, and `A_q`.
-/
def largeBaseFiberFloorLimit : Prop :=
  let energy : ℝ := ∫ t, ‖criticalResidual t‖ ^ 2 ∂criticalCauchyMeasure
  energy > 1 →
    Tendsto (fun q : ℕ => largeBase q) atTop (𝓝 0) ∧
    Tendsto (fun q : ℕ => fiberPeriod q) atTop (𝓝 0) ∧
    Tendsto
      (fun q : ℕ =>
        eLpNorm
          (fun t : ℝ => criticalBase q t - criticalResidual t)
          (2 : ℝ≥0∞) criticalCauchyMeasure)
      atTop (𝓝 0) ∧
    uniformlyReal (fun q x => fiberPeriod q * fiberD q x) 1 ∧
    uniformlyComplex
      (fun q x => (fiberPeriod q : ℂ) * fiberC q x) (1 : ℂ) ∧
    uniformlyReal (fun q x => fiberPeriod q * fiberA q x) energy ∧
    Tendsto (fun q : ℕ => fiberFloor q) atTop (𝓝 (1 - 1 / energy)) ∧
    0 < 1 - 1 / energy

end

end MathlibPlus.Open.Analysis
