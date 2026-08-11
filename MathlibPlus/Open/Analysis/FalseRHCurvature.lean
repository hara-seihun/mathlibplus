import Mathlib

/-!
# False-RH curvature counterfeit

A closed registry statement for the explicit `2 + cosh` counterfeit.
-/

namespace MathlibPlus.Open.Analysis.FalseRHCurvature

/-- The exact zero set, logarithmic-curvature sign, and first Jacobi-floor identity for the
`2 + cosh` counterfeit. The first squared Jacobi coefficient of the even weight is represented
by its normalized second moment. -/
def explicitCounterfeit : Prop :=
  let complexM : ℂ → ℂ := fun z => 2 + Complex.cosh z
  let realM : ℝ → ℝ := fun x => 2 + Real.cosh x
  let a : ℝ := Real.arcosh 2
  let mass : ℝ := ∫ x : ℝ, 1 / realM x
  let secondMoment : ℝ := ∫ x : ℝ, x ^ 2 / realM x
  let b1Sq : ℝ := secondMoment / mass
  (∀ z : ℂ, complexM z = 0 ↔
    ∃ sign k : ℤ, (sign = 1 ∨ sign = -1) ∧
      z = (sign : ℂ) * (a : ℂ) +
        ((2 * k + 1 : ℤ) : ℂ) * (Real.pi : ℂ) * Complex.I) ∧
  (∀ z : ℂ, complexM z = 0 → z.re ≠ 0) ∧
  (∀ x : ℝ, 0 < x →
    iteratedDeriv 3 (fun y : ℝ => Real.log (realM y)) x =
        -(2 * (Real.cosh x - 1) * Real.sinh x) / (2 + Real.cosh x) ^ 3 ∧
      -(2 * (Real.cosh x - 1) * Real.sinh x) / (2 + Real.cosh x) ^ 3 < 0) ∧
  MeasureTheory.Integrable (fun x : ℝ => 1 / realM x) ∧
  MeasureTheory.Integrable (fun x : ℝ => x ^ 2 / realM x) ∧
  0 < mass ∧
  iteratedDeriv 2 (fun y : ℝ => Real.log (realM y)) 0 * b1Sq =
      (Real.pi ^ 2 + a ^ 2) / 9 ∧
  (Real.pi ^ 2 + a ^ 2) / 9 < 4 / 3

end MathlibPlus.Open.Analysis.FalseRHCurvature
