import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NumberTheory.ZetaBatch

noncomputable section

private def mobiusSeries (x : ℝ) : ℝ :=
  ∑' n : ℕ,
    if n = 0 then 0
    else (ArithmeticFunction.moebius n : ℝ) * Real.exp (-(n : ℝ) * x)

private def transformedG (σ y : ℝ) : ℝ :=
  Real.exp (-σ * y) * mobiusSeries (Real.exp (-y))

private def transformedH (σ y : ℝ) : ℝ :=
  Real.exp (-σ * y) * Real.exp (-Real.exp (-y))

private def discreteOperator (σ : ℝ) (G : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∑' d : ℕ,
    if d = 0 then 0
    else Real.rpow (d : ℝ) (-σ) * G (y - Real.log (d : ℝ))

/-- Claim 46193: Möbius inversion and the discrete transformed equation. -/
def claim46193 : Prop :=
  (∀ x : ℝ, 0 < x →
    (∑' d : ℕ,
      if d = 0 then 0 else mobiusSeries ((d : ℝ) * x)) = Real.exp (-x)) ∧
    (∀ (σ y : ℝ), 0 < σ → σ < 1 →
      discreteOperator σ (transformedG σ) y = transformedH σ y)

private def qValue (s : ℂ) : ℂ :=
  (s - 1) * riemannZeta s - 1

/-- Claim 46201: the exact replay at `3/4+2i` exceeds `6/5`. -/
def claim46201 : Prop :=
  ‖qValue ((3 : ℂ) / 4 + 2 * Complex.I)‖ > (6 : ℝ) / 5

/-- Claim 46203: the unrotated real part is negative at the stated low height. -/
def claim46203 : Prop :=
  (((3 : ℂ) / 4 + (327 : ℂ) / 100 * Complex.I - 1) *
      riemannZeta ((3 : ℂ) / 4 + (327 : ℂ) / 100 * Complex.I)).re <
    -(1 : ℝ) / 2000

end
end MathlibPlus.Open.NumberTheory.ZetaBatch
