import MathlibPlus.Open.ResearchFormalization.R0629Claim26441

namespace MathlibPlus.Open.ResearchFormalization.R0629Claim26443

noncomputable section

open Classical
open MathlibPlus.Open.Graphs
open MathlibPlus.Open.ResearchFormalization.R0629Claim26441

/-- The coordinatewise deck signature after replacing every multiplicity by
`min(d_F,3)`. -/
def truncatedDeckSignature
    (G : GraphIsoClass 11) : GraphIsoClass 10 → ℕ :=
  fun F => min (deletionMultiplicity G F) 3

/-- Claim 26443: distinct retained graph columns have distinct exact
coordinatewise truncated deck signatures. -/
def claim26443 : Prop :=
  ∀ G H : GraphIsoClass 11,
    G ∈ retainedColumns → H ∈ retainedColumns → G ≠ H →
      truncatedDeckSignature G ≠ truncatedDeckSignature H

end

end MathlibPlus.Open.ResearchFormalization.R0629Claim26443
