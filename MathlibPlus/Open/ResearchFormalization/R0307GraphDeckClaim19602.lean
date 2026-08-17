import MathlibPlus.Open.Graphs.BasisTranspose

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0307GraphDeckClaim19602

noncomputable section

open MathlibPlus.Open.Graphs

private abbrev GraphSpace (n : ℕ) := GraphIsoClass n →₀ ℚ

private noncomputable def graphBasis {n : ℕ}
    (G : GraphIsoClass n) : GraphSpace n :=
  Finsupp.single G 1

/-- The full vertex-deletion deck of a graph-class basis vector. -/
noncomputable def fullVertexDeckBasis {n : ℕ}
    (G : GraphIsoClass (n + 1)) : GraphSpace n :=
  ∑ v : Fin (n + 1),
    graphBasis (graphClass (deleteGraph (graphRepresentative G) v))

/-- All-attachment insertion of a new vertex into a graph-class basis vector. -/
noncomputable def allAttachmentInsertionBasis {n : ℕ}
    (H : GraphIsoClass n) : GraphSpace (n + 1) :=
  ∑ S : Finset (Fin n),
    graphBasis (graphClass (insertGraph (graphRepresentative H) S))

/-- The full vertex deck operator on graph-isomorphism classes. -/
noncomputable def fullVertexDeck (n : ℕ) :
    GraphSpace (n + 1) →ₗ[ℚ] GraphSpace n :=
  Finsupp.linearCombination ℚ fullVertexDeckBasis

/-- The all-attachment insertion operator on graph-isomorphism classes. -/
noncomputable def allAttachmentInsertion (n : ℕ) :
    GraphSpace n →ₗ[ℚ] GraphSpace (n + 1) :=
  Finsupp.linearCombination ℚ allAttachmentInsertionBasis

end

end MathlibPlus.Open.ResearchFormalization.R0307GraphDeckClaim19602
