import MathlibPlus.Open.ResearchFormalization.RadialNestingDiscrepancyRepair

namespace MathlibPlus.Open.ResearchFormalization

open scoped BigOperators

noncomputable section

/-- Claim 10351: the full radial form is the completed-discrepancy pairing
with the prescribed Chebyshev, tail, and completed-constant terms. -/
def claim10351 : Prop :=
  ∀ (f : ℝ → ℝ), unitIntervalL2 f →
    ∀ t : ℝ, 0 < t →
      radialFull t f =
        ∫ u in Set.Ioc 0 (4 / t),
          (discrepancyQ u + discrepancyKappa - discrepancyAInfinity u) *
            deriv (fun v => testAutocorrelation (dilatedTest t f) v) u

end

end MathlibPlus.Open.ResearchFormalization
