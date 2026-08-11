import Mathlib.NumberTheory.Chebyshev

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-! Statement-fidelity registry node for admitted claim 1496. -/

/-- Claim 1496: the global absolute Chebyshev-psi bound with the displayed
amplitude, square-root exponential decay, and range `x > 2`. -/
def globalAbsolutePsiBoundWithSqrtLogDecay : Prop :=
  ∀ x : ℝ, 2 < x →
    |Chebyshev.psi x - x| <
      9.2202181 * x * Real.rpow (Real.log x) (3 / 2 : ℝ) *
        Real.exp (-(0.8817882 : ℝ) * Real.sqrt (Real.log x))

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
