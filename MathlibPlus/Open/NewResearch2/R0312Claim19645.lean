import MathlibPlus.Open.Graphs.BasisTranspose

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.R0312Flat

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

private noncomputable def pendantBasis {n : ℕ}
    (G : MathlibPlus.Open.Graphs.GraphIsoClass n) : GraphSpace (n + 1) :=
  ∑ v : Fin n,
    graphBasis
      (MathlibPlus.Open.Graphs.graphClass
        (MathlibPlus.Open.Graphs.insertGraph
          (MathlibPlus.Open.Graphs.graphRepresentative G)
          ({v} : Finset (Fin n))))

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

private noncomputable def pendantGraftOperator (n : ℕ) :
    GraphSpace n →ₗ[ℚ] GraphSpace (n + 1) :=
  Finsupp.linearCombination ℚ pendantBasis

private noncomputable def isolatedVertexOperator (n : ℕ) :
    GraphSpace n →ₗ[ℚ] GraphSpace (n + 1) :=
  Finsupp.linearCombination ℚ isolatedBasis

private noncomputable def deckFlatOperator (n : ℕ) :
    GraphSpace n →ₗ[ℚ] GraphSpace (n + 1) :=
  pendantGraftOperator n - (n : ℚ) • isolatedVertexOperator n

/-- Claim 19645: after subtracting the degree multiple of the isolated
extension, the pendant-graft operator commutes with the vertex deck. -/
def claim19645_elementaryDeckFlatRaisingOperator : Prop :=
  ∀ m : ℕ,
    (vertexDeckOperator (m + 1)).comp (deckFlatOperator (m + 1)) -
        (deckFlatOperator m).comp (vertexDeckOperator m) =
      (0 : GraphSpace (m + 1) →ₗ[ℚ] GraphSpace (m + 1))

end
end MathlibPlus.Open.NewResearch2.R0312Flat
