import MathlibPlus.Open.Analysis.LargeBaseFiberFloor

open scoped BigOperators ENNReal Interval Topology
open Filter MeasureTheory

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- The measurable periodic multipliers in the relaxed critical-line problem. -/
def measurablePeriodicMultiplier (T : ℝ) (g : ℝ → ℂ) : Prop :=
  Measurable g ∧ ∀ t : ℝ, g (t + T) = g t

/-- The relaxed periodic-fiber distance from the admitted critical-line carrier. -/
def relaxedPeriodicDistance (q : ℕ) : ℝ :=
  sInf {v : ℝ | ∃ g : ℝ → ℂ,
    measurablePeriodicMultiplier (fiberPeriod q) g ∧
      v = ∫ t : ℝ,
        ‖g t * criticalBase q t - 1‖ ^ 2 /
          (2 * Real.pi * ((1 : ℝ) / 4 + t ^ 2))}

/-- Exact fiberwise least squares for the relaxed periodic distance. -/
def exactFiberwiseLeastSquares : Prop :=
  ∀ q : ℕ, 2 ≤ q →
    relaxedPeriodicDistance q =
      ∫ x in (0 : ℝ)..fiberPeriod q,
        fiberD q x - ‖fiberC q x‖ ^ 2 / fiberA q x

/-- Constancy of the residual-base values along one period fiber. -/
def fiberValuesConstant (q : ℕ) (x : ℝ) : Prop :=
  ∃ c : ℂ, ∀ k : ℤ,
    criticalBase q (x + (k : ℝ) * fiberPeriod q) = c

/-- Equality in the weighted Cauchy--Schwarz inequality for one fiber. -/
def fiberCauchyEquality (q : ℕ) (x : ℝ) : Prop :=
  fiberA q x * fiberD q x = ‖fiberC q x‖ ^ 2

/-- A zero relaxed floor forces periodicity of the residual base. -/
def vanishingFloorForcesPeriodicity : Prop :=
  ∀ q : ℕ, 2 ≤ q →
    (∀ x : ℝ, x ∈ Set.Ico (0 : ℝ) (fiberPeriod q) →
      (fiberCauchyEquality q x ↔ fiberValuesConstant q x)) ∧
    (relaxedPeriodicDistance q = 0 →
      ∀ t : ℝ,
        criticalBase q (t + fiberPeriod q) = criticalBase q t)

end

end MathlibPlus.Open.Analysis
