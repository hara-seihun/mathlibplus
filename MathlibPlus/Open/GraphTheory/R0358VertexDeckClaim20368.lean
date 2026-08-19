import Mathlib
import MathlibPlus.Open.GraphTheory.R0358VertexDeckClaims

namespace MathlibPlus.Open.GraphTheory.R0358VertexDeck

noncomputable section

/-- Claim 20368: connected twelve-vertex, fifteen-edge graphs are determined up
to isomorphism by their full vertex deck with multiplicity. -/
def vertexDeckInjectivityAt12_15_claim20368 : Prop :=
  ∀ G H : Graph12,
    connectedWithEdgeCount 15 G →
    connectedWithEdgeCount 15 H →
    vertexDeckEqualByPermutation G H →
    Nonempty (G ≃g H)

end
end MathlibPlus.Open.GraphTheory.R0358VertexDeck
