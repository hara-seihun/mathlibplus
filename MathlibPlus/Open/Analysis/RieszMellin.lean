import Mathlib

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis

/-- The classical Riesz field on the positive-real series carrier. -/
def rieszField (x : ℝ) : ℝ :=
  x * ∑' n : {n : ℕ // 1 ≤ n},
    (ArithmeticFunction.moebius n.1 : ℝ) / (n.1 : ℝ) ^ 2 *
      Real.exp (-x / (n.1 : ℝ) ^ 2)

/-- Mellin transform identity for the classical Riesz field. -/
def mellinTransformRieszField : Prop :=
  ∀ s : ℂ,
    (1 : ℝ) / 2 < s.re →
    s.re < 1 →
    (∫ x in Set.Ioi (0 : ℝ),
        (rieszField x : ℂ) * Complex.cpow (x : ℂ) (-s - 1) ∂volume) =
      Complex.Gamma (1 - s) / riemannZeta (2 * s)

end MathlibPlus.Open.Analysis
