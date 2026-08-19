import MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting.ExactFixedHalfLineCoefficient
import MathlibPlus.Open.ResearchFormalization.C0064Claim976

namespace MathlibPlus.Open.ResearchFormalization.C0064Claim975

open MathlibPlus.Open.Analysis
open MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

noncomputable section

/-- Claim 975 on the reviewed 28-row Axler audit carrier. -/
def exactAuditNonStrictCoefficientCriterion_claim975 : Prop :=
  ∀ r ∈ auditRows,
    ∀ c : ℝ, c < Real.log (r.start : ℝ) →
      ((∀ x : ℝ, (r.start : ℝ) ≤ x →
          primeCountingReal x ≤ x / (Real.log x - c)) ↔
        sSup (auditScore_claim976 '' Set.Ici (r.start : ℝ)) ≤ c)

end

end MathlibPlus.Open.ResearchFormalization.C0064Claim975
