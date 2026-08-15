import Mathlib

namespace MathlibPlus.Open.Analysis

open Filter MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

private def fixedBasePeriod (q : ℕ) : ℝ :=
  2 * Real.pi / Real.log (q : ℝ)

private def fixedBaseRadius (q : ℕ) : ℝ :=
  Real.rpow (q : ℝ) (-1 / 2 : ℝ)

private def fixedBasePhi (q : ℕ) (z : ℂ) : ℂ :=
  Complex.exp
    (-((Real.log (q : ℝ) : ℂ) / 2) * ((1 + z) / (1 - z)))

private def fixedBaseZ (z : ℂ) : ℂ :=
  z * riemannZeta (1 / (1 - z))

private def fixedBaseH (q : ℕ) (z : ℂ) : ℂ :=
  fixedBaseZ z * (1 - (fixedBaseRadius q : ℂ) * fixedBasePhi q z) /
    (1 - (fixedBaseRadius q : ℂ) ^ 2)

private def fixedBaseCriticalPoint (t : ℝ) : ℂ :=
  1 - 1 / ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)

private def fixedBaseCriticalH (q : ℕ) (t : ℝ) : ℂ :=
  fixedBaseH q (fixedBaseCriticalPoint t)

private def fixedBaseCauchyDensity (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (2 * Real.pi * (1 / 4 + t ^ 2)))

private def fixedBaseCauchyMeasure : Measure ℝ :=
  Measure.withDensity volume fixedBaseCauchyDensity

private def fixedBaseLoss (q : ℕ) (g : ℝ → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ‖g t * fixedBaseCriticalH q t - 1‖ ^ 2

private def fixedBaseDelta (q : ℕ) : ℝ≥0∞ :=
  sInf {v : ℝ≥0∞ |
    ∃ g : ℝ → ℂ,
      Measurable g ∧ Function.Periodic g (fixedBasePeriod q) ∧
        v = ∫⁻ t, fixedBaseLoss q g t ∂fixedBaseCauchyMeasure}

/-- For every fixed integer base `q ≥ 2`, the relaxed periodic fiber minimum is positive. -/
def fixedBasePositiveFiberFloor : Prop :=
  ∀ q : ℕ, 2 ≤ q → 0 < fixedBaseDelta q

end
end MathlibPlus.Open.Analysis
