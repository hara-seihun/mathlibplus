import MathlibPlus.Open.GraphTheory.VertexDeckEdgeReconstruction
import MathlibPlus.GraphTheory.Claim20718

namespace MathlibPlus.GraphTheory

/-- The edge-count identity and quotient theorem in `Claim20718` prove the
registered vertex-deck reconstruction proposition after converting finite-set
edge cardinalities to `Set.ncard`. -/
theorem vertexDeckEdgeReconstruction_proved :
    MathlibPlus.Open.GraphTheory.vertexDeckEdgeReconstruction := by
  unfold MathlibPlus.Open.GraphTheory.vertexDeckEdgeReconstruction
  intro V _ G
  classical
  have h := MathlibPlus.GraphTheory.Claim20718.vertexDeckEdgeCountAndReconstruction G
  simpa [Set.ncard_eq_toFinset_card', SimpleGraph.edgeFinset] using h

end MathlibPlus.GraphTheory
