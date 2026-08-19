import MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803

open MathlibPlus.Open.OracleAreaOccupation

/-- The Dirac Boolean law at a driver. -/
def diracLaw (h : Driver n) : BooleanLaw n :=
  [(h, 1)]

/-- The finite-list law for `t δ_h + (1-t) ν`. -/
def radialMixture (t : ℝ) (h : Driver n) (nu : BooleanLaw n) : BooleanLaw n :=
  (diracLaw h).map (fun entry => (entry.1, t * entry.2)) ++
    nu.map (fun entry => (entry.1, (1 - t) * entry.2))

/-- The scalar functional `B` in the admitted radial-defect statement. -/
noncomputable def radialB (law : BooleanLaw n) : ℝ :=
  lawExpectation law (fun H => defect H (lawBarycentre law))

/-- The displayed radial defect for a Dirac insertion into a residual law. -/
noncomputable def radialDefect (t : ℝ) (h : Driver n) (nu : BooleanLaw n) : ℝ :=
  radialB (radialMixture t h nu) - (1 - t) ^ 2 * radialB nu

/-- The barycentre path attached to `t δ_h + (1-t) ν`. -/
def radialPoint (t : ℝ) (h : Driver n) (nu : BooleanLaw n) : Configuration n → ℝ :=
  fun ω => t * driverValue h ω + (1 - t) * lawBarycentre nu ω

/-- Claim 51609: the finite-law radial mixture has the displayed barycentre
and uses the complete-policy defect in the stated radial functional. -/
def claim51609 : Prop :=
  ∀ (n : ℕ) (nu : BooleanLaw n) (h : Driver n) (t : ℝ),
    isProbabilityLaw nu →
    0 ≤ t →
    t ≤ 1 →
    isProbabilityLaw (radialMixture t h nu) ∧
      lawBarycentre (radialMixture t h nu) = radialPoint t h nu

end MathlibPlus.Open.ResearchFormalization.AdaptiveOracleAreaR3803
