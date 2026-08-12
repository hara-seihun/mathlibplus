import MathlibPlus.Analysis.ThetaShellSummandClaim19068

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/-- Full source-level claim 19068.  The source calls the displayed positive
shell sum `Phi`; this registry node makes that identification and the
positive-index convention explicit for fidelity review. -/
def thetaSourcePositivity_claim19068 : Prop :=
  ∀ u : ℝ, 0 ≤ u →
    0 < ∑' m : {m : ℕ // 0 < m},
      MathlibPlus.Analysis.thetaShellSummand m.1 u

end MathlibPlus.Open.Analysis
