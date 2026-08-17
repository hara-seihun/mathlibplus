import MathlibPlus.Open.Analysis.NumeratorInnerOptimizationClaim3422

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- The complete off-line zeta Blaschke mass on the exact zero carrier used by
Claim 3413. -/
private noncomputable def zetaBlaschkeMass3417 : ℝ :=
  ∑' ρ : {z : ℂ //
      z ∈ riemannZetaZeros ∧ (1 / 2 : ℝ) < z.re},
    (analyticOrderNatAt riemannZeta ρ.1 : ℝ) *
      Real.log ‖ρ.1 / (1 - ρ.1)‖

/-- Zeta has no zero in the open half-plane to the right of the critical line. -/
private def zetaHasNoZeroRightOfCriticalLine3417 : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → ¬((1 / 2 : ℝ) < ρ.re)

/-- Claim 3417: vanishing of the exact off-line zeta mass is equivalent first
 to zero-freeness in `Re s > 1/2`, and then to the Riemann hypothesis. -/
def vanishingZetaMassEquivalentToRH_claim3417 : Prop :=
  (zetaBlaschkeMass3417 = 0 ↔
      zetaHasNoZeroRightOfCriticalLine3417) ∧
    (zetaHasNoZeroRightOfCriticalLine3417 ↔ RiemannHypothesis)

end

end MathlibPlus.Open.Analysis
