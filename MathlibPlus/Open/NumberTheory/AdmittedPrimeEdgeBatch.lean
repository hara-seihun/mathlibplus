import Mathlib

namespace MathlibPlus.Open.NumberTheory.FormalizationBatch

open Filter
open scoped BigOperators Topology

noncomputable def primeDirichletEdge (s : ℂ) : ℂ :=
  ∑' n : ℕ,
    if 2 ≤ n then
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        Complex.exp (-s * (Real.log (n : ℝ) : ℂ))
    else 0

noncomputable def deArchimedeanPrimeLogDerivative (s : ℂ) : ℂ :=
  -deriv riemannZeta s / riemannZeta s

/-- Claim 15455: the first-prime edge of the de-archimedeanized Xi channel. -/
def claim15455 : Prop :=
  (∀ s : ℂ, 1 < s.re →
    deArchimedeanPrimeLogDerivative s = primeDirichletEdge s) ∧
    ArithmeticFunction.vonMangoldt 2 = Real.log 2 ∧
    (∀ n : ℕ,
      ArithmeticFunction.vonMangoldt n ≠ 0 →
        Real.log 2 ≤ Real.log (n : ℝ)) ∧
    Tendsto
      (fun x : ℝ =>
        Complex.exp ((x : ℂ) * (Real.log 2 : ℂ)) *
          deArchimedeanPrimeLogDerivative (x : ℂ))
      atTop (𝓝 ((Real.log 2 : ℝ) : ℂ))

end MathlibPlus.Open.NumberTheory.FormalizationBatch
