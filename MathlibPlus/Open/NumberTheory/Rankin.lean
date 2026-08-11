import Mathlib

namespace MathlibPlus.Open.NumberTheory.Rankin

/-- The strict Rankin reflected-cone inequalities from admitted claim 289.

Here `τ(n)` is fixed without introducing a separate declaration: it is the `n`th
coefficient of the standard product
`X * ∏_{m ≥ 1} (1 - X^m)^24`.  Factors with `m > n` cannot affect that
coefficient, so the displayed finite product is the exact formal-power-series
normalization.  Also `n^(11/2)` is represented as `sqrt (n^11)`.
-/
def strictReflectedConeInequalities : Prop :=
  ∀ n : ℕ, 1 < n →
    let deltaTrunc : PowerSeries ℤ :=
      PowerSeries.X * ∏ m ∈ Finset.Icc 1 n, (1 - PowerSeries.X ^ m) ^ 24
    let tau : ℤ := PowerSeries.coeff n deltaTrunc
    let scale : ℝ := Real.sqrt ((n : ℝ) ^ 11)
    let A : ℝ := (ArithmeticFunction.sigma 11 n : ℝ) / scale
    let B : ℝ := (tau : ℝ) / scale
    let d : ℝ := (n.divisors.card : ℝ)
    A > d ∧ |B| ≤ d ∧
      A ^ 2 - B ^ 2 > 0 ∧
      A ^ 2 > 4 * d ∧
      A ^ 2 + B ^ 2 - 2 * d > 0 ∧
      A ^ 2 + 3 * B ^ 2 - 4 * d > 0

end MathlibPlus.Open.NumberTheory.Rankin
