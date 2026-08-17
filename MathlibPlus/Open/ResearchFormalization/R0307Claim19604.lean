import MathlibPlus.Open.Graphs.BasisTranspose

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0307Claim19604

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

noncomputable def insertionBasis {n : ℕ}
    (H : GraphIsoClass n) : GraphSpace (n + 1) :=
  ∑ S : Finset (Fin n),
    graphBasis (graphClass (insertGraph (graphRepresentative H) S))

noncomputable def deckOperator (n : ℕ) :
    GraphSpace (n + 1) →ₗ[ℚ] GraphSpace n :=
  Finsupp.linearCombination ℚ deletionBasis

noncomputable def insertionOperator (n : ℕ) :
    GraphSpace n →ₗ[ℚ] GraphSpace (n + 1) :=
  Finsupp.linearCombination ℚ insertionBasis

noncomputable def weightedPairing {n : ℕ}
    (x y : GraphSpace n) : ℚ :=
  ∑ G ∈ x.support,
    x G * y G * graphAutWeight n G

noncomputable def graphNormSquared (n : ℕ) (x : GraphSpace n) : ℚ :=
  weightedPairing x x

/-- The automorphism-weighted insertion energy identity, including the
zero-level boundary and the displayed predecessor-level indexing. -/
def claim_19604 : Prop :=
  (∀ x : GraphSpace 0,
    graphNormSquared 1 (insertionOperator 0 x) =
      graphNormSquared 0 x) ∧
    ∀ (n : ℕ) (x : GraphSpace (n + 1)),
      graphNormSquared (n + 2) (insertionOperator (n + 1) x) =
        2 * graphNormSquared n (deckOperator n x) +
          (2 : ℚ) ^ (n + 1) * graphNormSquared (n + 1) x

end

end MathlibPlus.Open.ResearchFormalization.R0307Claim19604
