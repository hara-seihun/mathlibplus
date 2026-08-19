import Mathlib
import MathlibPlus.Open.Research.CIAtlas
import MathlibPlus.Open.ResearchFormalization.R0980Claim27863

namespace MathlibPlus.Open.ResearchFormalization.R0980Claim27864

noncomputable section
open Classical

abbrev G27864 := MathlibPlus.Open.Research.CIAtlas.C2CubedC9

private def connectedPartitionBreaking27864 (S : Finset G27864) : Prop :=
  MathlibPlus.Open.Research.CIAtlas.graphConnected72 S ∧
    MathlibPlus.Open.ResearchFormalization.R0980.partitionBreaking27863 S

private def connectedNonlinearBase27864 (S : Finset G27864) : Prop :=
  MathlibPlus.Open.Research.CIAtlas.graphConnected72 S ∧
    MathlibPlus.Open.ResearchFormalization.R0980.nonlinearBase27863 S

/-- Claim 27864: within the exact valency-thirteen ordinary graph-type
    carrier, connected partition-breaking and connected nonlinear-base types
    occur in the stated positive numbers. -/
def claim27864 : Prop :=
  ∃ R : Finset (Finset G27864),
    MathlibPlus.Open.ResearchFormalization.R0980.graphTypeRepresentatives27863 R ∧
    (R.filter connectedPartitionBreaking27864).card = 1032 ∧
    (R.filter connectedNonlinearBase27864).card = 92 ∧
    (∃ S, S ∈ R ∧
      MathlibPlus.Open.Research.CIAtlas.connectionSet72 13 S ∧
      MathlibPlus.Open.Research.CIAtlas.graphConnected72 S ∧
      MathlibPlus.Open.ResearchFormalization.R0980.partitionBreaking27863 S) ∧
    (∃ S, S ∈ R ∧
      MathlibPlus.Open.Research.CIAtlas.connectionSet72 13 S ∧
      MathlibPlus.Open.Research.CIAtlas.graphConnected72 S ∧
      MathlibPlus.Open.ResearchFormalization.R0980.nonlinearBase27863 S)

end
end MathlibPlus.Open.ResearchFormalization.R0980Claim27864
