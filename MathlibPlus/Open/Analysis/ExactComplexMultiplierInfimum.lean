import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace MathlibPlus.Open.Analysis

/-- Claim 44129: exact complex multiplier-cost infimum and its strict-cost criterion. -/
def exactComplexMultiplierInfimum : Prop :=
  ∀ (S : ℂ) (ε : ℝ), 0 ≤ ε →
    sInf (Set.range (fun M : ℂ => ‖M * S - 1‖ + ε * ‖M‖)) =
        (if S = 0 then 1 else min 1 (ε / ‖S‖)) ∧
    ((∃ M : ℂ, ‖M * S - 1‖ + ε * ‖M‖ < 1) ↔ ‖S‖ > ε)

end MathlibPlus.Open.Analysis
