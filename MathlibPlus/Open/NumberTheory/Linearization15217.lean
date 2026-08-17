import Mathlib
import MathlibPlus.NumberTheory.Claim15213

open scoped BigOperators

namespace MathlibPlus.Open.NumberTheory.Linearization15217

noncomputable section

/-- The pointwise Selberg recursion formula, with the source's arithmetic
function and Dirichlet-convolution carriers made explicit. -/
def selbergRecursionValue (a : ArithmeticFunction ℝ) (n : ℕ) : ℝ :=
  a n * Real.log n + (a * a) n

/-- The linear term at the von Mangoldt arithmetic function. -/
def linearizedSelbergValue (h : ArithmeticFunction ℝ) (n : ℕ) : ℝ :=
  h n * Real.log n +
    2 * ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) * h) n

/-- The ordinary Dirichlet series attached to a real arithmetic function. -/
noncomputable def arithmeticDirichletSeries
    (a : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑' n : {n : ℕ // 1 ≤ n},
    (a n.1 : ℂ) * Complex.cpow (n.1 : ℂ) (-s)

/-- The logarithmic derivative carrier used in the right half-plane. -/
noncomputable def zetaLogDerivative (s : ℂ) : ℂ :=
  -(deriv riemannZeta s) / riemannZeta s

/-- Claim 15217: the explicit pointwise derivative of the Selberg recursion
at von Mangoldt and its two linked Dirichlet-series identities in
`Re s > 1`. -/
def claim15217_linearizationAtVonMangoldt : Prop :=
  (∀ (a : ArithmeticFunction ℝ) (ha : a 1 = 0) (n : ℕ),
    selbergRecursionValue a n =
      MathlibPlus.NumberTheory.Claim15213.selbergRecursion a ha n) ∧
  ∀ h : ArithmeticFunction ℝ, h 1 = 0 →
    (∀ n : ℕ,
      HasDerivAt
        (fun ε : ℝ =>
          selbergRecursionValue
            ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) + ε • h) n)
        (linearizedSelbergValue h n) 0) ∧
      (∀ s : ℂ, 1 < s.re →
        let H : ℂ → ℂ := arithmeticDirichletSeries h
        let R : ℂ → ℂ :=
          arithmeticDirichletSeries
            (fun n => linearizedSelbergValue h n)
        let B : ℂ → ℂ := zetaLogDerivative
        R s = -(deriv H s) + 2 * B s * H s ∧
          deriv (fun z : ℂ => riemannZeta z ^ 2 * H z) s =
            -riemannZeta s ^ 2 * R s)

end

end MathlibPlus.Open.NumberTheory.Linearization15217
