import MathlibPlus.Open.ResearchFormalization.R1404CarryAtlas

namespace MathlibPlus.Open.ResearchFormalization.R1404TransporterCounts38677

open MathlibPlus.Open.ResearchFormalization.R1404

noncomputable section

abbrev NormalizedAtlasRow :=
  {row : BasePosition × (BasePoint → ZMod 3) // normalizedCarry row.2}

abbrev SuccessfulAtlasRow :=
  {row : NormalizedAtlasRow // definingTransporterInClosure row.1.1 row.1.2}

/-- Claim 38677: among the exact normalized carry atlas rows, the defining
transporter belongs to the generated directed binary two-closure in exactly
58477 rows and misses in exactly 572 rows. -/
def claim38677 : Prop :=
  Nat.card BasePosition = 9 ∧
    Nat.card {g : BasePoint → ZMod 3 // normalizedCarry g} = 6561 ∧
    Nat.card NormalizedAtlasRow = 59049 ∧
    Nat.card SuccessfulAtlasRow = 58477 ∧
    Nat.card atlasFailureRows = 572

end

end MathlibPlus.Open.ResearchFormalization.R1404TransporterCounts38677
