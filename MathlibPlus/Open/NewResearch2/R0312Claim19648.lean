import MathlibPlus.Open.Graphs.BasisTranspose

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.R0312Subset

noncomputable section

private abbrev GraphSpace (n : ℕ) :=
  MathlibPlus.Open.Graphs.GraphIsoClass n →₀ ℚ

private noncomputable def graphBasis {n : ℕ}
    (G : MathlibPlus.Open.Graphs.GraphIsoClass n) : GraphSpace n :=
  Finsupp.single G 1

private noncomputable def subsetAdjunctionBasis
    (c : ℕ → ℚ) {n : ℕ}
    (G : MathlibPlus.Open.Graphs.GraphIsoClass n) : GraphSpace (n + 1) :=
  ∑ S : Finset (Fin n),
    c S.card •
      graphBasis
        (MathlibPlus.Open.Graphs.graphClass
          (MathlibPlus.Open.Graphs.insertGraph
            (MathlibPlus.Open.Graphs.graphRepresentative G) S))

/-- Claim 19648: for weights depending only on the chosen subset cardinality,
the vertex-adjunction operator has exactly the displayed basis action. -/
def claim19648_generalSubsetWeightedVertexAdjunctionOperator
    (c : ℕ → ℚ)
    (A : ∀ n : ℕ, GraphSpace n →ₗ[ℚ] GraphSpace (n + 1)) : Prop :=
  ∀ n : ℕ,
    ∀ G : MathlibPlus.Open.Graphs.GraphIsoClass n,
      A n (graphBasis G) = subsetAdjunctionBasis c G

end
end MathlibPlus.Open.NewResearch2.R0312Subset
