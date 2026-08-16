import MathlibPlus.Open.ResearchFormalization.GeometricKernel

open scoped BigOperators Interval Topology
open MeasureTheory
open Filter

namespace MathlibPlus.Open.ResearchFormalization

noncomputable def zetaBlaschkeMultiplicity (ρ : ℂ) : ℕ :=
  analyticOrderNatAt riemannZeta ρ

noncomputable def zetaBlaschkeDefect : ℝ :=
  ∑' ρ : {ρ : ℂ // ρ ∈ riemannZetaZeros ∧ (1 / 2 : ℝ) < (ρ.1 : ℂ).re},
    (zetaBlaschkeMultiplicity ρ.1 : ℝ) *
      Real.log ‖ρ.1 / (1 - ρ.1)‖

noncomputable def geometricKnownBlaschkeMass (q : ℕ) : ℝ :=
  ∑' k : ℕ,
    Real.log
      (1 + (Real.log (q : ℝ)) ^ 2 /
        (4 * Real.pi ^ 2 * ((k + 1 : ℕ) : ℝ) ^ 2))

/-- Claim 15281: the exact Poisson--Jensen/H² budget after subtracting
its complete geometric zero divisor, together with the resulting closed
form bound for the off-line zeta defect. -/
def claim_15281 : Prop :=
  ∀ q : ℕ, 2 ≤ q →
    geometricKnownBlaschkeMass q =
        Real.log
          (Real.sinh (Real.log (q : ℝ) / 2) /
            (Real.log (q : ℝ) / 2)) ∧
      Real.log (Real.log (q : ℝ)) +
          geometricKnownBlaschkeMass q + zetaBlaschkeDefect ≤
        (1 / 2 : ℝ) * Real.log (geometricN q) ∧
      zetaBlaschkeDefect ≤
        (1 / 2 : ℝ) * Real.log
          (((q : ℝ) * geometricN q) / ((q : ℝ) - 1) ^ 2)

end MathlibPlus.Open.ResearchFormalization
