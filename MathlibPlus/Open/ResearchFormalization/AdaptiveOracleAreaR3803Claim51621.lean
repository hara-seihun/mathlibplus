import MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803Claim51621

open MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803
open MathlibPlus.Open.OracleAreaOccupation

/-- Claim 51621: the active-face identity is the law-weighted star
circulation, with the full self-row expression retained when the row at h
uses the active policy rho. -/
def claim51621 : Prop :=
  ∀ (n : ℕ) (law : BooleanLaw n) (h : Driver n)
    (u : Configuration n → ℝ)
    (rho : DeterministicPolicy n)
    (pi : Driver n → DeterministicPolicy n),
    lawRepresents law u →
    activePolicy h u rho →
    (∀ entry ∈ law,
      directionalActive entry.1 h u (pi entry.1)) →
    let T : Driver n → DeterministicPolicy n → Driver n → ℝ :=
      fun K p H =>
        2 * policyBilinear p u (driverValue H) -
          constrainedValue K u - qCost K
    let circulation : ℝ :=
      lawExpectation law (fun K =>
        T K (pi K) h + T h rho K)
    let selfRow : ℝ := T h rho h + T h rho h
    let selfExpression : ℝ :=
      -2 * (qCost h - policyArea rho (driverValue h) +
        policyArea rho (fun ω => driverValue h ω - u ω))
    policyArea rho u = constrainedValue h u ∧
      lawExpectation law (fun K => T h rho K) = defect h u ∧
      score law h = circulation ∧
      (pi h = rho → selfRow = selfExpression ∧ selfExpression ≤ 0)

end MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803Claim51621
