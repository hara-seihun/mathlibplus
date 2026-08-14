import Mathlib

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Research.Mellin

/-- The double Mellin transform of the first triangular kernel. -/
def doubleMellinLeft (w v : ℂ) : ℂ :=
  ∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
    ((x / (x + y) : ℝ) : ℂ) *
      Complex.exp (-(x + y : ℝ)) *
      Complex.cpow (x : ℂ) (w - 1) *
      Complex.cpow (y : ℂ) (v - 1)

/-- The transposed triangular Mellin kernel. -/
def doubleMellinRight (w v : ℂ) : ℂ :=
  ∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
    ((y / (x + y) : ℝ) : ℂ) *
      Complex.exp (-(x + y : ℝ)) *
      Complex.cpow (x : ℂ) (w - 1) *
      Complex.cpow (y : ℂ) (v - 1)

/-- Claim 7258: the exact double Mellin transform. -/
def claim7258 : Prop :=
  ∀ w v : ℂ,
    0 < w.re →
    0 < v.re →
    doubleMellinLeft w v = Complex.Gamma w * Complex.Gamma v * w / (w + v)

/-- Claim 7260: transposition exchanges the two Mellin exponents. -/
def claim7260 : Prop :=
  ∀ w v : ℂ,
    0 < w.re →
    0 < v.re →
    doubleMellinRight w v = Complex.Gamma w * Complex.Gamma v * v / (w + v)

end MathlibPlus.Open.Research.Mellin

end
