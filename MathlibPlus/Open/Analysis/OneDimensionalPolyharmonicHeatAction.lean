import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- The saddle constant for the one-dimensional symbol `ξ ^ (2m)`. -/
def polyharmonicSaddleConstant (m : ℕ) : ℝ :=
  let mr : ℝ := m
  (2 * mr - 1) * Real.rpow (2 * mr) (-(2 * mr) / (2 * mr - 1)) *
    Real.sin (Real.pi / (4 * mr - 2))

/-- The complex phase of the one-dimensional polyharmonic Fourier integrand. -/
def oneDimensionalPolyharmonicPhase (m : ℕ) (α x : ℝ) (z : ℂ) : ℂ :=
  -(α : ℂ) * z ^ (2 * m) + Complex.I * (x : ℂ) * z

/-- The steepest-descent saddle selected by the decaying branch of the phase. -/
def oneDimensionalPolyharmonicSaddle (m : ℕ) (α x : ℝ) : ℂ :=
  let mr : ℝ := m
  let radius : ℝ :=
    Real.rpow (|x| / (2 * mr * α)) (1 / (2 * mr - 1))
  let angle : ℝ := Real.pi / (4 * mr - 2)
  (radius : ℂ) *
    Complex.exp
      ((Complex.I : ℂ) *
        (((if 0 ≤ x then (1 : ℝ) else -1) * angle) : ℂ))

/-- The exponential action supplied by the decaying saddle of the phase. -/
def oneDimensionalPolyharmonicHeatAction (m : ℕ) (α x : ℝ) : ℝ :=
  -(oneDimensionalPolyharmonicPhase m α x
      (oneDimensionalPolyharmonicSaddle m α x)).re

/--
For every positive fixed order and heat time, the sharp one-dimensional
polyharmonic exponential action at `x` has the stated value.
-/
def oneDimensionalFixedOrderPolyharmonicHeatAction : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (α x : ℝ), 0 < α →
    oneDimensionalPolyharmonicHeatAction m α x =
      polyharmonicSaddleConstant m *
        Real.rpow α (-(1 / (2 * (m : ℝ) - 1))) *
        Real.rpow |x| ((2 * (m : ℝ)) / (2 * (m : ℝ) - 1))

end

end MathlibPlus.Open.Analysis
