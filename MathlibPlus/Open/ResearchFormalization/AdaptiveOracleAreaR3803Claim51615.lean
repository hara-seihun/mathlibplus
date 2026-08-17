import MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803.Claim51615

open MathlibPlus.Open.OracleAreaOccupation
open MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803

/-- The policy-quadratic polarization identity and its directional-active
finite-law expansion, with every disagreement term evaluated by the same
complete policy. -/
def policyQuadraticAndDirectionalExpansion : Prop :=
  (∀ (n : ℕ) (d : DeterministicPolicy n)
      (u : Configuration n → ℝ) (h : Driver n),
    2 * policyBilinear d u (driverValue h) - policyArea d u =
      policyArea d (driverValue h) -
        policyArea d (fun ω => driverValue h ω - u ω)) ∧
  (∀ (n : ℕ) (law : BooleanLaw n) (h : Driver n)
      (pi : Driver n → DeterministicPolicy n),
    isProbabilityLaw law →
      (∀ entry ∈ law,
        directionalActive entry.1 h (lawBarycentre law) (pi entry.1)) →
      score law h =
        defect h (lawBarycentre law) +
          lawExpectation law (fun K =>
            policyArea (pi K) (driverValue h) - qCost K -
              policyArea (pi K)
                (fun ω => driverValue h ω - lawBarycentre law ω)))

end MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803.Claim51615
