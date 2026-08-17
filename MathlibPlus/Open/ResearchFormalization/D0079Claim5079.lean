import MathlibPlus.Open.Combinatorics.ResearchFormalizationBatch_01a00449_34ca_760c_84ef_ba44bc77fc60

namespace MathlibPlus.Open.ResearchFormalizationD0079

/-- Claim 5079: the bounded connected-tree motif channels have the displayed
kernel/intersection defect on the rational unlabelled-tree state space. -/
def claim5079 : Prop :=
  ∀ (n q : ℕ),
    MathlibPlus.Open.Combinatorics.motifObservabilityDefect n q =
        LinearMap.ker
          (MathlibPlus.Open.Combinatorics.observabilityMap n q) ∧
      MathlibPlus.Open.Combinatorics.motifObservabilityDefect n q =
        ⨅ H : MathlibPlus.Open.Combinatorics.RetainedMotif q,
          LinearMap.ker
            (MathlibPlus.Open.Combinatorics.motifChannel n q H)

end MathlibPlus.Open.ResearchFormalizationD0079
