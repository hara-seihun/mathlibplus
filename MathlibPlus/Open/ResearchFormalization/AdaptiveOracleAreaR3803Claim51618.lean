import MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803Claim51618

open MathlibPlus.Open.OracleAreaOccupation
open MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803

noncomputable section

/-- The exact active symmetric tangent from the R-3803 pair condition. -/
def tangentTerm (u : Configuration n → ℝ) (K h : Driver n)
    (pi : DeterministicPolicy n) : ℝ :=
  2 * policyBilinear pi u (driverValue h) - constrainedValue K u - qCost K

def pairCondition (u : Configuration n → ℝ) : Prop :=
  ∀ (h K : Driver n) (rho : DeterministicPolicy n),
    activePolicy h u rho →
      ∃ pi : DeterministicPolicy n,
        activePolicy K u pi ∧
          tangentTerm u K h pi + tangentTerm u h K rho ≤ 0

/-- The finite-law radial defect used by the source's contraction inequality. -/
noncomputable def radialDefect (law : BooleanLaw n) : ℝ :=
  lawExpectation law (fun H => defect H (lawBarycentre law))

def blendLaw (t : ℝ) (h : Driver n) (nu : BooleanLaw n) : BooleanLaw n :=
  [(h, t)] ++ nu.map (fun entry => (entry.1, (1 - t) * entry.2))

def universalPairCondition : Prop :=
  ∀ (n : ℕ) (u : Configuration n → ℝ), pairCondition u

/-- Claim 51618: the universal active-pair choice gives the exact affine
majorant of the active score coefficient, its barycentric value, score
nonpositivity, and the resulting finite-law radial contraction. -/
def affineMajorantAndRadialContraction_claim51618 : Prop :=
  (∀ (n : ℕ) (law : BooleanLaw n) (u : Configuration n → ℝ),
    lawRepresents law u →
      pairCondition u →
        ∀ (h : Driver n) (rho : DeterministicPolicy n),
          activePolicy h u rho →
            ∃ a : AffineForm n,
              (∀ K : Driver n,
                affineValue a (driverValue K) =
                  qCost h + constrainedValue h u -
                    2 * policyBilinear rho u (driverValue K)) ∧
              (∀ K : Driver n,
                directionalMinimum K h u ≤
                  affineValue a (driverValue K)) ∧
              affineValue a u = -defect h u ∧
              score law h ≤ 0) ∧
  (universalPairCondition →
    ∀ (n : ℕ) (nu : BooleanLaw n) (h : Driver n) (t : ℝ),
      isProbabilityLaw nu →
        0 ≤ t → t ≤ 1 →
          radialDefect (blendLaw t h nu) ≤
            (1 - t) ^ 2 * radialDefect nu)

end

end MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803Claim51618
