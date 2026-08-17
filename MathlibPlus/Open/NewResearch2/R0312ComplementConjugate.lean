import MathlibPlus.Open.Graphs.BasisTranspose

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.R0312ComplementConjugate

noncomputable section
open Classical

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

private noncomputable def subsetAdjunctionOperator
    (c : ℕ → ℚ) (n : ℕ) :
    GraphSpace n →ₗ[ℚ] GraphSpace (n + 1) :=
  Finsupp.linearCombination ℚ (subsetAdjunctionBasis c)

private noncomputable def complementConjugateWeight
    (n j : ℕ) : ℚ :=
  if j + 1 = n then 1 else if j = n then -(n : ℚ) else 0

private noncomputable def complementConjugateOperator (n : ℕ) :
    GraphSpace n →ₗ[ℚ] GraphSpace (n + 1) :=
  subsetAdjunctionOperator (complementConjugateWeight n) n

private noncomputable def isolatedBasis {n : ℕ}
    (G : MathlibPlus.Open.Graphs.GraphIsoClass n) : GraphSpace (n + 1) :=
  graphBasis
    (MathlibPlus.Open.Graphs.graphClass
      (MathlibPlus.Open.Graphs.insertGraph
        (MathlibPlus.Open.Graphs.graphRepresentative G)
        (∅ : Finset (Fin n))))

private noncomputable def pendantBasis {n : ℕ}
    (G : MathlibPlus.Open.Graphs.GraphIsoClass n) : GraphSpace (n + 1) :=
  ∑ v : Fin n,
    graphBasis
      (MathlibPlus.Open.Graphs.graphClass
        (MathlibPlus.Open.Graphs.insertGraph
          (MathlibPlus.Open.Graphs.graphRepresentative G)
          ({v} : Finset (Fin n))))

private noncomputable def isolatedVertexOperator (n : ℕ) :
    GraphSpace n →ₗ[ℚ] GraphSpace (n + 1) :=
  Finsupp.linearCombination ℚ isolatedBasis

private noncomputable def pendantGraftOperator (n : ℕ) :
    GraphSpace n →ₗ[ℚ] GraphSpace (n + 1) :=
  Finsupp.linearCombination ℚ pendantBasis

private noncomputable def deckFlatOperator (n : ℕ) :
    GraphSpace n →ₗ[ℚ] GraphSpace (n + 1) :=
  pendantGraftOperator n - (n : ℚ) • isolatedVertexOperator n

private noncomputable def complementClass {n : ℕ}
    (G : MathlibPlus.Open.Graphs.GraphIsoClass n) :
    MathlibPlus.Open.Graphs.GraphIsoClass n :=
  MathlibPlus.Open.Graphs.graphClass
    (MathlibPlus.Open.Graphs.graphRepresentative G)ᶜ

private noncomputable def complementOperator (n : ℕ) :
    GraphSpace n →ₗ[ℚ] GraphSpace n :=
  Finsupp.linearCombination ℚ
    (fun G => graphBasis (complementClass G))

/-- Claim 19654: the codimension-one-minus-full subset-adjunction operator is
complement-conjugate to the pendant-graft-minus-isolation operator. -/
def claim19654_complementConjugateClosedForm : Prop :=
  ∀ n : ℕ,
    (complementOperator (n + 1)).comp
        (complementConjugateOperator n) =
      (deckFlatOperator n).comp (complementOperator n)

end
end MathlibPlus.Open.NewResearch2.R0312ComplementConjugate
