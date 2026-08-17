import MathlibPlus.Open.Combinatorics.PositiveRedundancyClaim15612
import MathlibPlus.Open.ResearchFormalization.GraphDeckBatch

namespace MathlibPlus.Open.ResearchFormalization.R2781

/-- Claim 31501: the exact order-twelve redundancy-zero relation is detected
by a full cover row and is not the tree-count difference of a deck-equal,
nonisomorphic graph pair. -/
def claim31501 : Prop :=
  let fullKocayKernel :
      (MathlibPlus.Open.Combinatorics.PositiveRedundancy.TreeType12 → ℤ) → Prop :=
    fun w =>
      ∀ {k : ℕ}
        (F : Fin k → MathlibPlus.Open.Combinatorics.PositiveRedundancy.GraphMotif),
        MathlibPlus.Open.Combinatorics.PositiveRedundancy.properFamily F →
          ∑ T : MathlibPlus.Open.Combinatorics.PositiveRedundancy.TreeType12,
            w T * MathlibPlus.Open.Combinatorics.PositiveRedundancy.coverRow F T = 0
  ∃ w : MathlibPlus.Open.Combinatorics.PositiveRedundancy.TreeType12 → ℤ,
    MathlibPlus.Open.Combinatorics.PositiveRedundancy.exactKernelVector w ∧
      (∃ (k : ℕ)
          (F : Fin k → MathlibPlus.Open.Combinatorics.PositiveRedundancy.GraphMotif),
        MathlibPlus.Open.Combinatorics.PositiveRedundancy.redundancyOneFamily F ∧
          ∑ T : MathlibPlus.Open.Combinatorics.PositiveRedundancy.TreeType12,
            w T * MathlibPlus.Open.Combinatorics.PositiveRedundancy.coverRow F T ≠ 0) ∧
      ¬ fullKocayKernel w ∧
      ¬ ∃ G H : SimpleGraph (Fin 12),
        MathlibPlus.Open.ResearchFormalization.vertexDeckEqual G H ∧
          ¬ Nonempty (G ≃g H) ∧
          ∀ T : MathlibPlus.Open.Combinatorics.PositiveRedundancy.TreeType12,
            (MathlibPlus.Open.ResearchFormalization.ordinarySubgraphCount
                (MathlibPlus.Open.Combinatorics.PositiveRedundancy.representativeGraph T) G : ℤ) -
                (MathlibPlus.Open.ResearchFormalization.ordinarySubgraphCount
                  (MathlibPlus.Open.Combinatorics.PositiveRedundancy.representativeGraph T) H : ℤ) =
              w T

end MathlibPlus.Open.ResearchFormalization.R2781
