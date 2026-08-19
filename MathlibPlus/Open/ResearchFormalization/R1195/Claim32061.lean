import MathlibPlus.Open.ResearchBatchHallControls

namespace MathlibPlus.Open.ResearchFormalization.R1195.Claim32061

open MathlibPlus.Open.ResearchBatchHallControls

/-- The concrete `Gm m` operation has the displayed `C_m ⋊ C₈`
presentation: `gmA` and `gmB` satisfy their orders and the inversion
relation, with the exact group-operation carrier retained. -/
def claim32061 (m : ℕ) : Prop :=
  gmGroupAxioms m ∧ gmPresentationRelations m

end MathlibPlus.Open.ResearchFormalization.R1195.Claim32061
