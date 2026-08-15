import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis

/--
The nonnegative trigonometric packet for a finite positive mixture of shifted
logarithmic derivatives, with all of the data in the admitted statement kept
explicit.
-/
def nonnegativeTrigonometricPacket : Prop :=
  ∀ (μ : Measure NNReal),
    IsFiniteMeasure μ →
    ∀ (m : ℕ) (a : ℕ → ℝ) (σ T : ℝ),
      (∀ k : ℕ, k ≤ m → 0 ≤ a k) →
      0 < a 1 →
      (1 < σ) →
      let P : ℝ → ℝ :=
        fun v => a 0 + ∑ k ∈ Finset.Icc (1 : ℕ) m, a k * Real.cos ((k : ℝ) * v)
      let fμ : ℝ → ℝ :=
        fun u => ∫ r : NNReal, Real.exp (-((r : ℝ) * u)) ∂μ
      let Dμ : ℂ → ℂ :=
        fun s =>
          ∫ r : NNReal,
            (-deriv riemannZeta (s + (r : ℂ))) /
              riemannZeta (s + (r : ℂ)) ∂μ
      (∀ v : ℝ, 0 ≤ P v) →
        (∑ k ∈ Finset.range (m + 1), a k * Complex.re
            (Dμ ((σ : ℂ) + Complex.I * ((k : ℂ) * (T : ℂ)))) =
          ∑' n : ℕ,
            if 2 ≤ n then
              (ArithmeticFunction.vonMangoldt n) * ((n : ℝ) ^ (-σ)) *
                fμ (Real.log (n : ℝ)) * P (T * Real.log (n : ℝ))
            else 0) ∧
        0 ≤
          ∑' n : ℕ,
            if 2 ≤ n then
              (ArithmeticFunction.vonMangoldt n) * ((n : ℝ) ^ (-σ)) *
                fμ (Real.log (n : ℝ)) * P (T * Real.log (n : ℝ))
            else 0

end MathlibPlus.Open.Analysis
