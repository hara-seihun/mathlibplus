import Mathlib.NumberTheory.Chebyshev

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-! Statement-fidelity registry node for admitted claim 1499. -/

/-- Claim 1499: the preceding strict global absolute Chebyshev-psi envelope. -/
def globalAbsolutePsiBoundWithSqrtLogDecay_claim1499 : Prop :=
  ∀ x : ℝ, 2 < x →
    |Chebyshev.psi x - x| <
      9.2202181 * x * Real.rpow (Real.log x) (3 / 2 : ℝ) *
        Real.exp (-(0.88178 : ℝ) * Real.sqrt (Real.log x))

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
