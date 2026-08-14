import Mathlib

open scoped BigOperators
open MeasureTheory
open ProbabilityTheory

namespace MathlibPlus.Open.Analysis

/-- The law of a Gamma random variable with shape `1/2` and rate `1`. -/
noncomputable def gammaHalfLaw : Measure ℝ :=
  volume.withDensity (ProbabilityTheory.gammaPDF ((1 : ℝ) / 2) 1)

/-- The moments `E[(y + Z)^(2j)]` for `Z ~ Gamma(1/2, 1)`. -/
noncomputable def gammaHalfP (j : ℕ) (y : ℝ) : ℝ :=
  ∫ z : ℝ, (y + z) ^ (2 * j) ∂gammaHalfLaw

/-- The five points `y_i = 6/5 + i/100`, indexed by `0 ≤ i < 5`. -/
noncomputable def gammaHalfY (i : Fin 5) : ℝ :=
  6 / 5 + ((i : ℕ) : ℝ) / 100

/-- The determinant of the `P_0, ..., P_4` evaluation matrix at five points. -/
noncomputable def gammaHalfDet (x : Fin 5 → ℝ) : ℝ :=
  Matrix.det (fun (i j : Fin 5) => gammaHalfP (j : ℕ) (x i))

/-- Positivity of every ordered evaluation determinant on an open interval. -/
def gammaHalfStrictChebyshevOn (a b : ℝ) : Prop :=
  ∀ x : Fin 5 → ℝ,
    StrictMono x →
    (∀ i : Fin 5, a < x i ∧ x i < b) →
    0 < gammaHalfDet x

/-- The universal strict-Chebyshev target on the third logarithmic cell. -/
def gammaHalfUniversalStrictChebyshevTarget : Prop :=
  gammaHalfStrictChebyshevOn (Real.log 3) (Real.log 4)

/--
The admitted Gamma-half determinant counterexample: the specified points lie in
`(log 3, log 4)`, the evaluation determinant has the stated negative exact
value, and the corresponding strict-Chebyshev conclusions fail.
-/
def gammaHalfInitialFlagCounterexample : Prop :=
  (∀ i : Fin 5,
    gammaHalfY i = 6 / 5 + ((i : ℕ) : ℝ) / 100) ∧
  Real.log 3 < gammaHalfY 0 ∧
  gammaHalfY 0 < gammaHalfY 1 ∧
  gammaHalfY 1 < gammaHalfY 2 ∧
  gammaHalfY 2 < gammaHalfY 3 ∧
  gammaHalfY 3 < gammaHalfY 4 ∧
  gammaHalfY 4 < Real.log 4 ∧
  gammaHalfDet gammaHalfY =
    -(191088130123149778791 : ℝ) /
      48828125000000000000000000000000000 ∧
  (-(191088130123149778791 : ℝ) /
      48828125000000000000000000000000000) < 0 ∧
  ¬ gammaHalfStrictChebyshevOn (Real.log 3) (Real.log 4) ∧
  ¬ gammaHalfUniversalStrictChebyshevTarget

end MathlibPlus.Open.Analysis
