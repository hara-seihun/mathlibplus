import MathlibPlus.Open.Graphs.BasisTranspose

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0307GraphCommutatorClaim19603

noncomputable section

open MathlibPlus.Open.Graphs

private abbrev GraphSpace (n : ℕ) := GraphIsoClass n →₀ ℚ

private noncomputable def graphBasis {n : ℕ}
    (G : GraphIsoClass n) : GraphSpace n :=
  Finsupp.single G 1

private noncomputable def deletionBasis {n : ℕ}
    (G : GraphIsoClass (n + 1)) : GraphSpace n :=
  ∑ v : Fin (n + 1),
    graphBasis (graphClass (deleteGraph (graphRepresentative G) v))

private noncomputable def insertionBasis {n : ℕ}
    (H : GraphIsoClass n) : GraphSpace (n + 1) :=
  ∑ S : Finset (Fin n),
    graphBasis (graphClass (insertGraph (graphRepresentative H) S))

private noncomputable def deckOperator (n : ℕ) :
    GraphSpace (n + 1) →ₗ[ℚ] GraphSpace n :=
  Finsupp.linearCombination ℚ deletionBasis

private noncomputable def insertionOperator (n : ℕ) :
    GraphSpace n →ₗ[ℚ] GraphSpace (n + 1) :=
  Finsupp.linearCombination ℚ insertionBasis

/-- Claim 19603: on every graph level, including the level-zero boundary,
    the full-attachment insertion and vertex-deck operators satisfy the exact
    q-two commutator. -/
def exactQTwoGraphDeckCommutator_claim19603 : Prop :=
  (deckOperator 0).comp (insertionOperator 0) =
      (LinearMap.id : GraphSpace 0 →ₗ[ℚ] GraphSpace 0) ∧
    ∀ n : ℕ,
      (deckOperator (n + 1)).comp (insertionOperator (n + 1)) -
          (2 : ℚ) • (insertionOperator n).comp (deckOperator n) =
        (2 : ℚ) ^ (n + 1) •
          (LinearMap.id : GraphSpace (n + 1) →ₗ[ℚ] GraphSpace (n + 1))

end

end MathlibPlus.Open.ResearchFormalization.R0307GraphCommutatorClaim19603
