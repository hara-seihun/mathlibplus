import MathlibPlus.Open.Graphs.BasisTranspose

open scoped BigOperators

namespace MathlibPlus.Open.Research.GraphReconstructionExact

noncomputable section

open MathlibPlus.Open.Graphs

abbrev GraphSpace (n : ℕ) := GraphIsoClass n →₀ ℚ

noncomputable def graphBasis {n : ℕ}
    (G : GraphIsoClass n) : GraphSpace n :=
  Finsupp.single G 1

noncomputable def deletionBasis {n : ℕ}
    (G : GraphIsoClass (n + 1)) : GraphSpace n :=
  ∑ v : Fin (n + 1),
    graphBasis (graphClass (deleteGraph (graphRepresentative G) v))

noncomputable def deckOperator (n : ℕ) :
    GraphSpace (n + 1) →ₗ[ℚ] GraphSpace n :=
  Finsupp.linearCombination ℚ deletionBasis

def deckSignature {n : ℕ} (G : GraphIsoClass (n + 1)) : GraphSpace n :=
  deletionBasis G

def vertexReconstructibleAt (n : ℕ) : Prop :=
  ∀ G H : GraphIsoClass (n + 1), G ≠ H →
    deckSignature G ≠ deckSignature H

/-- At each positive graph level, reconstruction is exactly the exclusion of
nonzero basis differences from the fixed vertex-deck kernel. -/
def claim19607 : Prop :=
  ∀ n : ℕ,
    vertexReconstructibleAt n ↔
      ∀ G H : GraphIsoClass (n + 1), G ≠ H →
        Finsupp.single G (1 : ℚ) - Finsupp.single H (1 : ℚ) ∉
          LinearMap.ker (deckOperator n)

end
end MathlibPlus.Open.Research.GraphReconstructionExact
