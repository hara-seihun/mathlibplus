import MathlibPlus.Open.ResearchFormalizationBatch.Claim22231

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization.R0517Claim22230

noncomputable section

private abbrev DeckCoeff := MvPolynomial (Fin 2) ℤ

private def specializedComponentWeight (s : ℕ) : DeckCoeff :=
  if s = 1 then
    MvPolynomial.C 1 + MvPolynomial.X 0
  else
    MvPolynomial.C 1 + MvPolynomial.X 0 * (MvPolynomial.X 1) ^ (s - 1)

private def deckFactorSeries {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : Polynomial DeckCoeff :=
  ∑ C ∈ T.edgeFinset.powerset,
    Polynomial.C ((-(1 : DeckCoeff)) ^ (T.edgeFinset.card - C.card)) *
      (Polynomial.X : Polynomial DeckCoeff) ^ C.card *
      Polynomial.C (∑ K ∈
        (MathlibPlus.Open.ResearchFormalizationBatch.componentSets
          (T.deleteEdges (C : Set (Sym2 V)))).filter
          (fun K => K.ncard = 1),
        ∏ J ∈
          (MathlibPlus.Open.ResearchFormalizationBatch.componentSets
            (T.deleteEdges (C : Set (Sym2 V)))).erase K,
          specializedComponentWeight J.ncard)

private def xqCoefficient (P : Polynomial DeckCoeff) (s : ℕ) : Polynomial ℤ :=
  ∑ k ∈ P.support,
    Polynomial.C ((P.coeff k).coeff
      (Finsupp.single (0 : Fin 2) 1 +
        Finsupp.single (1 : Fin 2) (s - 1))) *
      Polynomial.X ^ k

private def boundaryEdgeSet {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (S : Finset V) : Set (Sym2 V) :=
  {e | e ∈ T.edgeSet ∧
    ∃ x ∈ S, ∃ y, y ∉ S ∧ e = s(x, y)}

private def vertexStarEdgeSet {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (v : V) : Set (Sym2 V) :=
  {e | e ∈ T.edgeSet ∧ ∃ y, e = s(v, y)}

private def boundaryUnionSize {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (S : Finset V) (v : V) : ℕ :=
  (boundaryEdgeSet T S ∪ vertexStarEdgeSet T v).ncard

private def connectedPairCount {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (s h : ℕ) : ℕ :=
  Nat.card {p : V × Finset V //
    p.2.Nonempty ∧
      p.2.card = s ∧
        p.2 ≠ (Finset.univ : Finset V) ∧
          p.1 ∉ p.2 ∧
            (T.induce (p.2 : Set V)).Connected ∧
              boundaryUnionSize T p.2 p.1 = h}

/-- Claim 22230: the exact `X Q^(s-1)` coefficient of the normalized deck
factor series is the signed Bernstein combination of the ordered connected
proper-subset/outsider counts. -/
def claim22230_bernsteinConnectedSubsetCoefficient : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V), T.IsTree →
    ∀ s : ℕ, 0 < s → s < Fintype.card V →
      xqCoefficient (deckFactorSeries T) s =
        (-1 : Polynomial ℤ) ^ (s - 1) *
          ∑ h ∈ Finset.range (Fintype.card V - s + 1),
            Polynomial.C (connectedPairCount T s h : ℤ) *
              (Polynomial.X : Polynomial ℤ) ^ h *
                (Polynomial.X - 1) ^ (Fintype.card V - s - h)

end

end MathlibPlus.Open.ResearchFormalization.R0517Claim22230
