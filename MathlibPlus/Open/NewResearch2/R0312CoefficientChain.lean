import MathlibPlus.Open.Graphs.BasisTranspose

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.R0312CoefficientChain

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

private noncomputable def subsetAdjunctionBasis
    (c : ℕ → ℚ) {n : ℕ}
    (G : MathlibPlus.Open.Graphs.GraphIsoClass n) : GraphSpace (n + 1) :=
  ∑ S : Finset (Fin n),
    c S.card •
      graphBasis
        (MathlibPlus.Open.Graphs.graphClass
          (MathlibPlus.Open.Graphs.insertGraph
            (MathlibPlus.Open.Graphs.graphRepresentative G) S))

private noncomputable def subsetAdjunctionOperator
    (c : ℕ → ℚ) (n : ℕ) :
    GraphSpace n →ₗ[ℚ] GraphSpace (n + 1) :=
  Finsupp.linearCombination ℚ (subsetAdjunctionBasis c)

private def coefficientSupported (c : ℕ → ℕ → ℚ) : Prop :=
  ∀ n j, n < j → c n j = 0

private def coefficientCompatible (c : ℕ → ℕ → ℚ) : Prop :=
  ∀ n j, c n j = c (n + 1) j + c (n + 1) (j + 1)

private noncomputable def coefficientScalar
    (c : ℕ → ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℚ) * c n j

private def coefficientScalarVanishing (c : ℕ → ℕ → ℚ) : Prop :=
  ∀ n, coefficientScalar c n = 0

private def deckFlatChain (c : ℕ → ℕ → ℚ) : Prop :=
  (vertexDeckOperator 0).comp
        (subsetAdjunctionOperator (fun j => c 0 j) 0) =
      (0 : GraphSpace 0 →ₗ[ℚ] GraphSpace 0) ∧
    ∀ n : ℕ,
      (vertexDeckOperator (n + 1)).comp
          (subsetAdjunctionOperator (fun j => c (n + 1) j) (n + 1)) =
        (subsetAdjunctionOperator (fun j => c n j) n).comp
          (vertexDeckOperator n)

private def coefficientChainValid (c : ℕ → ℕ → ℚ) : Prop :=
  coefficientSupported c ∧ coefficientCompatible c ∧ deckFlatChain c

/-- Claim 19650: the coefficient-chain recurrence and the vanishing scalar
criterion are exactly the deck-flatness condition for the cardinality-weighted
subset-adjunction chain. -/
def claim19650 : Prop :=
  ∀ c : ℕ → ℕ → ℚ,
    coefficientSupported c →
      (deckFlatChain c ↔
        coefficientScalarVanishing c ∧ coefficientCompatible c)

/-- Claim 19652: after the forced level-zero value, each positive level has one
free diagonal scalar, and those diagonal scalars determine the chain. -/
def claim19652 : Prop :=
  (∀ a : ℕ → ℚ, a 0 = 0 →
    ∃ c : ℕ → ℕ → ℚ,
      coefficientChainValid c ∧ ∀ n, c n n = a n) ∧
    ∀ c d : ℕ → ℕ → ℚ,
      coefficientChainValid c →
        coefficientChainValid d →
          (∀ n, 1 ≤ n → c n n = d n n) → c = d

end
end MathlibPlus.Open.NewResearch2.R0312CoefficientChain
