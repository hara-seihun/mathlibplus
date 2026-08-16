import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchTriangle11925

noncomputable section

/-- The compactly supported triangle from the packet's Fourier convention. -/
def triangle (u : ℝ) : ℝ := max (1 - |u|) 0

/-- Fourier transform using the packet's `exp(i z u)` convention. -/
def triangleHat (z : ℂ) : ℂ :=
  ∫ u : ℝ, (triangle u : ℂ) * Complex.exp (Complex.I * z * (u : ℂ))

def triangleQuotientFormula (z : ℂ) : ℂ :=
  if z = 0 then 1 else 2 * (1 - Complex.cos z) / z^2

def triangleSincSquareFormula (z : ℂ) : ℂ :=
  if z = 0 then 1 else (Complex.sin (z / 2) / (z / 2))^2

/-- Analytic vanishing to exactly order two. -/
def hasExactDoubleZero (f : ℂ → ℂ) (a : ℂ) : Prop :=
  AnalyticAt ℂ f a ∧
    f a = 0 ∧
    HasDerivAt f 0 a ∧
    ∃ v : ℂ, HasDerivAt (deriv f) v a ∧ v ≠ 0

/-- The triangle transform, its removable origin value, and its complete
nonzero double-root description. -/
def triangleFourierTransformClaim : Prop :=
  (triangleHat 0 = 1) ∧
  (∀ z : ℂ,
    triangleHat z = triangleQuotientFormula z ∧
    triangleHat z = triangleSincSquareFormula z) ∧
  (∀ z : ℂ, triangleHat z = 0 → z ≠ 0 →
    ∃ k : ℤ, k ≠ 0 ∧ z = (2 : ℂ) * (Real.pi : ℂ) * (k : ℂ)) ∧
  (∀ k : ℤ, k ≠ 0 →
    hasExactDoubleZero triangleHat ((2 : ℂ) * (Real.pi : ℂ) * (k : ℂ)))

end

end MathlibPlus.Open.ResearchFormalization.BatchTriangle11925
