import MathlibPlus.Open.Graphs.BasisTranspose

namespace MathlibPlus.Open.NewResearch2.R0312ComplementDeck

noncomputable section
open Classical

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

private noncomputable def vertexDeckOperator (n : ℕ) :
    GraphSpace (n + 1) →ₗ[ℚ] GraphSpace n :=
  Finsupp.linearCombination ℚ deletionBasis

private noncomputable def complementClass {n : ℕ}
    (G : MathlibPlus.Open.Graphs.GraphIsoClass n) :
    MathlibPlus.Open.Graphs.GraphIsoClass n :=
  MathlibPlus.Open.Graphs.graphClass
    (MathlibPlus.Open.Graphs.graphRepresentative G)ᶜ

private noncomputable def complementOperator (n : ℕ) :
    GraphSpace n →ₗ[ℚ] GraphSpace n :=
  Finsupp.linearCombination ℚ (fun G => graphBasis (complementClass G))

/-- Claim 19653: complementation is equivariant for the vertex-deck operator in
all graph degrees. -/
def claim19653 : Prop :=
  ∀ n : ℕ,
    (vertexDeckOperator n).comp (complementOperator (n + 1)) =
      (complementOperator n).comp (vertexDeckOperator n)

end
end MathlibPlus.Open.NewResearch2.R0312ComplementDeck
