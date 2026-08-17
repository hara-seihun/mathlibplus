import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.R0108Claim18008

open scoped BigOperators

noncomputable section

private abbrev BivariateSeries := MvPowerSeries (Fin 2) ℝ

private def firstAxis (H : PowerSeries ℝ) : BivariateSeries :=
  MvPowerSeries.rename (fun _ : Unit => (0 : Fin 2)) H

private def secondAxis (H : PowerSeries ℝ) : BivariateSeries :=
  MvPowerSeries.rename (fun _ : Unit => (1 : Fin 2)) H

/-- The formal product `H(z) H(w)` in two variables. -/
private def bivariateProduct (H : PowerSeries ℝ) : BivariateSeries :=
  firstAxis H * secondAxis H

/-- The formal relative Euler current
`(w ∂_w - z ∂_z)(H(z) H(w))`. -/
private def relativeEulerCurrent (H : PowerSeries ℝ) : BivariateSeries :=
  MvPowerSeries.X (1 : Fin 2) *
      MvPowerSeries.pderiv ℝ (1 : Fin 2) (bivariateProduct H) -
    MvPowerSeries.X (0 : Fin 2) *
      MvPowerSeries.pderiv ℝ (0 : Fin 2) (bivariateProduct H)

private def swapVariables (J : BivariateSeries) : BivariateSeries :=
  MvPowerSeries.renameEquiv ℝ (Equiv.swap (0 : Fin 2) 1) J

private def bidegree (a b : ℕ) : (Fin 2 →₀ ℕ) :=
  Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b

private def diagonalEvaluation (J : BivariateSeries) (z : ℝ) : ℝ :=
  ∑' p : ℕ × ℕ,
    MvPowerSeries.coeff (bidegree p.1 p.2) J * z ^ (p.1 + p.2)

private def diagonalEvaluable (J : BivariateSeries) (z : ℝ) : Prop :=
  Summable (fun p : ℕ × ℕ =>
    MvPowerSeries.coeff (bidegree p.1 p.2) J * z ^ (p.1 + p.2))

/-- Claim 18008: the Euler score current is antisymmetric, has zero diagonal
coefficients, and its formal diagonal evaluation is zero whenever that
series evaluation is defined. -/
def claim18008 : Prop :=
  ∀ (H : PowerSeries ℝ),
    swapVariables (relativeEulerCurrent H) =
        -relativeEulerCurrent H ∧
      (∀ a : ℕ,
        MvPowerSeries.coeff (bidegree a a) (relativeEulerCurrent H) = 0) ∧
      (∀ z : ℝ,
        diagonalEvaluable (relativeEulerCurrent H) z →
          diagonalEvaluation (relativeEulerCurrent H) z = 0)

end

end MathlibPlus.Open.FormalizationBatch.R0108Claim18008
