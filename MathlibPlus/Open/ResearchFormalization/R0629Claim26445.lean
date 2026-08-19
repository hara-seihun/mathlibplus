import MathlibPlus.Open.ResearchFormalization.R0629Claim26441

namespace MathlibPlus.Open.ResearchFormalization.R0629Claim26445

noncomputable section

open Classical
open MathlibPlus.Open.Graphs
open MathlibPlus.Open.ResearchFormalization.R0629Claim26441

/-- Coordinatewise congruence modulo four of the retained raw deck vectors. -/
def deckCongruentModuloFour
    (G H : GraphIsoClass 11) : Prop :=
  ∀ F : GraphIsoClass 10,
    deletionMultiplicity G F % 4 = deletionMultiplicity H F % 4

/-- The retained residue class through one retained graph column. -/
def retainedResidueClass
    (G : GraphIsoClass 11) : Finset (GraphIsoClass 11) :=
  retainedColumns.filter (fun H => deckCongruentModuloFour G H)

/-- Claim 26445: every coordinatewise-modulo-four residue class in the exact
retained graph-column carrier has at most four members. -/
def claim26445 : Prop :=
  ∀ G : GraphIsoClass 11,
    G ∈ retainedColumns →
      (retainedResidueClass G).card ≤ 4

end

end MathlibPlus.Open.ResearchFormalization.R0629Claim26445
