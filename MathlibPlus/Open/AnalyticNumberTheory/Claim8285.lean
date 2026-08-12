import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace MathlibPlus.Open.AnalyticNumberTheory

open scoped BigOperators

/--
Claim 8285.  The displayed sums are indexed by positive integers (`k + 1`),
which makes the conventional meaning of sums over `(a,N)=1` explicit.  The
source excerpt does not state the convergence domain; the node exposes the
standard `0 < N`, `0 < x`, and `0 < y` hypotheses rather than hiding them in
an analytic API, and leaves both exact reductions as one open proposition.
-/
def oneDimensionalMellinReductionsClaim8285 : Prop :=
  ∀ (N : ℕ) (x y : ℝ), 0 < N → 0 < x → 0 < y →
    let M : ℝ → ℝ := fun t ↦
      ∑' k : ℕ,
        if Nat.Coprime (k + 1) N then
          (((ArithmeticFunction.moebius (k + 1) : ℤ) : ℝ) /
              ((k + 1 : ℕ) : ℝ)) *
            Real.exp (-t * ((k + 1 : ℕ) : ℝ))
        else 0
    let L : ℝ → ℝ := fun t ↦
      ∑' k : ℕ,
        if Nat.Coprime (k + 1) N then
          Real.exp (-t * ((k + 1 : ℕ) : ℝ)) /
            ((k + 1 : ℕ) : ℝ)
        else 0
    let K : ℝ → ℝ → ℝ := fun x' y' ↦
      ∑' k : ℕ,
        if Nat.Coprime (k + 1) N then
          (Real.exp (-y' * ((k + 1 : ℕ) : ℝ)) /
              ((k + 1 : ℕ) : ℝ)) *
            M (((k + 1 : ℕ) : ℝ) * x')
        else 0
    L y =
        -N.divisors.sum (fun d ↦
          (((ArithmeticFunction.moebius d : ℤ) : ℝ) /
              (d : ℝ)) *
            Real.log (1 - Real.exp (-(d : ℝ) * y))) ∧
      K x y =
        ∑' k : ℕ,
          if Nat.Coprime (k + 1) N then
            (((ArithmeticFunction.moebius (k + 1) : ℤ) : ℝ) /
                ((k + 1 : ℕ) : ℝ)) *
              L (y + x * ((k + 1 : ℕ) : ℝ))
          else 0

end MathlibPlus.Open.AnalyticNumberTheory
