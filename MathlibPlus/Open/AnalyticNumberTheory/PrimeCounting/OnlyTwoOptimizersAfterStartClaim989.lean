import MathlibPlus.Open.Analysis.PrimeCountingRepairs

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

open MathlibPlus.Open.Analysis

/-- Claim 989: in the concrete Axler audit table, exactly the two displayed
optimizers lie strictly after their published starts. -/
def onlyTwoOptimizersAfterStart_claim989 : Prop :=
  auditRows.length = 28 ∧
    (auditRows.filter (fun r => r.optimizer = r.start)).length = 26 ∧
    (auditRows.filter (fun r => r.start < r.optimizer)).length = 2 ∧
    (∀ r ∈ auditRows,
      r.start < r.optimizer ↔
        ((r.publishedCoeff = (1077 : ℝ) / 1000 ∧
            r.optimizer = 7117303 ∧
            r.piOptimizer = 484136 ∧
            Nat.primeCounting 7117303 = 484136) ∨
          (r.publishedCoeff = (1078 : ℝ) / 1000 ∧
            r.optimizer = 5465671 ∧
            r.piOptimizer = 378614 ∧
            Nat.primeCounting 5465671 = 378614)))

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
