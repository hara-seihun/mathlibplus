import Mathlib

/-!
# Hardy-Z nonvanishing at the integer endpoints

This registry node records admitted claim 270 from legacy packet `C-0017`.
The decimal centers and radii are exact rationals in Lean. Both certified real
intervals and the resulting Hardy-Z and zeta nonvanishing conclusions are retained.
-/

namespace MathlibPlus.Open.AnalyticNumberTheory.HardyZ

/-- The certified Hardy-Z enclosures at `T₀ = 3000175332800` and `T₁ = T₀ + 1`
exclude zero, so neither critical-line endpoint is a zeta zero. -/
noncomputable def endpointNonvanishing : Prop :=
  let theta : ℝ → ℝ := fun t =>
    (Complex.log (Complex.Gamma
      ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ)))).im
      - t / 2 * Real.log Real.pi
  let zetaPoint : ℝ → ℂ := fun t =>
    riemannZeta ((1 / 2 : ℂ) + Complex.I * (t : ℂ))
  let hardyZComplex : ℝ → ℂ := fun t =>
    Complex.exp (Complex.I * ((theta t : ℝ) : ℂ)) * zetaPoint t
  let hardyZ : ℝ → ℝ := fun t => (hardyZComplex t).re
  let T₀ : ℝ := 3000175332800
  let T₁ : ℝ := 3000175332801
  let center₀ : ℝ :=
    -2.57247883265165580632636171109680207668879374098265087114460844
  let radius₀ : ℝ := 359 / 10 ^ 65
  let center₁ : ℝ :=
    -0.336136705815223584910795182704075498002622139676253786211841651
  let radius₁ : ℝ := 421 / 10 ^ 66
  (hardyZComplex T₀).im = 0 ∧
    (hardyZComplex T₁).im = 0 ∧
    center₀ - radius₀ ≤ hardyZ T₀ ∧
    hardyZ T₀ ≤ center₀ + radius₀ ∧
    center₁ - radius₁ ≤ hardyZ T₁ ∧
    hardyZ T₁ ≤ center₁ + radius₁ ∧
    hardyZ T₀ < 0 ∧ hardyZ T₁ < 0 ∧
    hardyZComplex T₀ ≠ 0 ∧ hardyZComplex T₁ ≠ 0 ∧
    zetaPoint T₀ ≠ 0 ∧ zetaPoint T₁ ≠ 0

end MathlibPlus.Open.AnalyticNumberTheory.HardyZ
