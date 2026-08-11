import Mathlib.NumberTheory.Chebyshev

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-! Statement-fidelity registry node for admitted claim 1067. -/

/-- Claim 1067: the global absolute Chebyshev-psi bound with prefactor
`0.026 * x * L^1.801` and the displayed
`r(L)=L^(3/5)/(log L)^(1/5)` exponential scale, with range `x ≥ 23`.
The quotient is kept explicit rather than replaced by an equivalent expression.
-/
def globalAbsolutePsiBoundWithLogLogScale : Prop :=
  ∀ x : ℝ, 23 ≤ x →
    let L := Real.log x
    |Chebyshev.psi x - x| <
      0.026 * x * Real.rpow L (1.801 : ℝ) *
        Real.exp (-(0.2043 : ℝ) *
          (Real.rpow L (3 / 5 : ℝ) /
            Real.rpow (Real.log L) (1 / 5 : ℝ)))

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
