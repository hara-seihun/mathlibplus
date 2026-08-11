import Mathlib.NumberTheory.Chebyshev

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeSums

/-!
Statement-fidelity formalization of admitted claim 1022.  The source's `ψ` is
Mathlib's `Chebyshev.psi`.  Its displayed equivalent `Eψ` notation is not
defined in the claim text, so it is represented here by the absolute normalized
error `|(ψ x - x) / x|`.  The fractional power is `Real.rpow`, and all decimal
constants are exact rationals.
-/

/-- Global absolute Chebyshev-`ψ` decay with the displayed coefficient and rate. -/
def globalPsiAbsoluteDecay : Prop :=
  ∀ x : ℝ, 2 < x →
    (|(Chebyshev.psi x - x)| <
        (92202181 / 10000000 : ℝ) * x *
          Real.rpow (Real.log x) (3 / 2 : ℝ) *
          Real.exp (-(88178 / 100000 : ℝ) * Real.sqrt (Real.log x))) ∧
      (|((Chebyshev.psi x - x) / x)| <
        (92202181 / 10000000 : ℝ) *
          Real.rpow (Real.log x) (3 / 2 : ℝ) *
          Real.exp (-(88178 / 100000 : ℝ) * Real.sqrt (Real.log x)))

end MathlibPlus.Open.AnalyticNumberTheory.PrimeSums
