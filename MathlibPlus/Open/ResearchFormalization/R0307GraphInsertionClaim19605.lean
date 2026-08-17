import MathlibPlus.Open.Graphs.BasisTranspose

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0307GraphInsertionClaim19605

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

/-- The automorphism-weighted diagonal pairing on each graph-class basis. -/
private noncomputable def weightedPairing {n : ℕ}
    (x y : GraphSpace n) : ℚ :=
  ∑ G ∈ x.support,
    x G * y G * graphAutWeight n G

private noncomputable def weightedLength {n : ℕ} (x : GraphSpace n) : ℝ :=
  Real.sqrt (weightedPairing x x : ℝ)

/-- Claim 19605: the all-attachment insertion has the stated least-singular-
    value floor in the automorphism-weighted norm, and its weighted adjoint
    vertex deck is respectively injective and surjective. -/
def graphInsertionInjectivityAndDeckSurjectivity_claim19605 : Prop :=
  ∀ n : ℕ,
    (∀ x : GraphSpace n,
      0 ≤ weightedPairing x x ∧
        (weightedPairing x x = 0 ↔ x = 0)) ∧
    (∀ x : GraphSpace n, ∀ y : GraphSpace (n + 1),
      weightedPairing (insertionOperator n x) y =
        weightedPairing x (deckOperator n y)) ∧
    (∀ x : GraphSpace n,
      Real.rpow 2 ((n : ℝ) / 2) * weightedLength x ≤
        weightedLength (insertionOperator n x)) ∧
    Function.Injective (insertionOperator n) ∧
    Function.Surjective (deckOperator n)

end

end MathlibPlus.Open.ResearchFormalization.R0307GraphInsertionClaim19605
