import MathlibPlus.Open.Graphs.BasisTranspose

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.R0312

noncomputable section

private abbrev GraphSpace (n : ℕ) :=
  MathlibPlus.Open.Graphs.GraphIsoClass n →₀ ℚ

private noncomputable def graphBasis {n : ℕ}
    (G : MathlibPlus.Open.Graphs.GraphIsoClass n) : GraphSpace n :=
  Finsupp.single G 1

private noncomputable def deletionBasis {n : ℕ}
    (G : MathlibPlus.Open.Graphs.GraphIsoClass (n + 1)) : GraphSpace n :=
  ∑ v : Fin (n + 1),
    graphBasis
      (MathlibPlus.Open.Graphs.graphClass
        (MathlibPlus.Open.Graphs.deleteGraph
          (MathlibPlus.Open.Graphs.graphRepresentative G) v))

private noncomputable def isolatedBasis {n : ℕ}
    (G : MathlibPlus.Open.Graphs.GraphIsoClass n) : GraphSpace (n + 1) :=
  graphBasis
    (MathlibPlus.Open.Graphs.graphClass
      (MathlibPlus.Open.Graphs.insertGraph
        (MathlibPlus.Open.Graphs.graphRepresentative G)
        (∅ : Finset (Fin n))))

private noncomputable def vertexDeckOperator (n : ℕ) :
    GraphSpace (n + 1) →ₗ[ℚ] GraphSpace n :=
  Finsupp.linearCombination ℚ deletionBasis

private noncomputable def isolatedVertexOperator (n : ℕ) :
    GraphSpace n →ₗ[ℚ] GraphSpace (n + 1) :=
  Finsupp.linearCombination ℚ isolatedBasis

/-- Claim 19643: adjoining an isolated vertex and then taking the vertex deck
is the identity plus taking the deck first and adjoining an isolate. -/
def claim19643_isolationDeletionCommutator : Prop :=
  (vertexDeckOperator 0).comp (isolatedVertexOperator 0) =
      (LinearMap.id : GraphSpace 0 →ₗ[ℚ] GraphSpace 0) ∧
    ∀ m : ℕ,
      (vertexDeckOperator (m + 1)).comp
          (isolatedVertexOperator (m + 1)) =
        (LinearMap.id : GraphSpace (m + 1) →ₗ[ℚ] GraphSpace (m + 1)) +
          (isolatedVertexOperator m).comp (vertexDeckOperator m)

end
end MathlibPlus.Open.NewResearch2.R0312
