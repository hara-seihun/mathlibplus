import MathlibPlus.Open.ResearchFormalization.R0629Claim26441

namespace MathlibPlus.Open.ResearchFormalization.R0629Claim26444

noncomputable section

open Classical
open MathlibPlus.Open.Graphs
open MathlibPlus.Open.ResearchFormalization.R0629Claim26441

/-- A pair of retained columns is a stopping set exactly when no cubic
support-feature row is supported by one member of the pair alone. -/
def cubicPairStoppingSet
    (G H : GraphIsoClass 11) : Prop :=
  G ∈ retainedColumns ∧ H ∈ retainedColumns ∧ G ≠ H ∧
    ∀ f : Multiset (GraphIsoClass 10),
      (cubicCardFeature G f ↔ cubicCardFeature H f)

/-- Claim 26444: no distinct pair of retained graph columns is a stopping set
for the exact cubic support incidence relation. -/
def claim26444 : Prop :=
  ∀ G H : GraphIsoClass 11,
    G ∈ retainedColumns → H ∈ retainedColumns → G ≠ H →
      ¬ cubicPairStoppingSet G H

end

end MathlibPlus.Open.ResearchFormalization.R0629Claim26444
