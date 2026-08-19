import MathlibPlus.Open.ResearchFormalization.R0629Claim26441

namespace MathlibPlus.Open.ResearchFormalization.R0629Claim26439

noncomputable section

open Classical
open MathlibPlus.Open.Graphs
open MathlibPlus.Open.ResearchFormalization.R0629Claim26441

/-- The exact row carrier of the restricted complete cubic-support matrix. -/
def supportedCubicFeature
    (f : Multiset (GraphIsoClass 10)) : Prop :=
  ∃ G : GraphIsoClass 11,
    G ∈ retainedColumns ∧ cubicCardFeature G f

/-- The exact nonzero graph-feature incidence carrier. -/
def retainedCubicIncidence
    (G : GraphIsoClass 11) (f : Multiset (GraphIsoClass 10)) : Prop :=
  G ∈ retainedColumns ∧ cubicCardFeature G f

/-- Claim 26439: the retained block has exactly the displayed column, row,
and nonzero-incidence cardinalities, with all three carriers tied to the
reviewed deletion-multiplicity support relation. -/
def claim26439 : Prop :=
  retainedColumns.card = 2640 ∧
    Nat.card {f : Multiset (GraphIsoClass 10) //
      supportedCubicFeature f} = 251216 ∧
      Nat.card
          {p : GraphIsoClass 11 × Multiset (GraphIsoClass 10) //
            retainedCubicIncidence p.1 p.2} = 256556

end

end MathlibPlus.Open.ResearchFormalization.R0629Claim26439
