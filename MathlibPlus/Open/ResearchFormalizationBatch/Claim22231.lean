import Mathlib
import MathlibPlus.Open.Combinatorics.AdmittedForestBatch

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalizationBatch

noncomputable section

private abbrev DeckCoeff := MvPolynomial (Fin 2) ℤ

/-- The component weight after the singleton variable is specialized to
`1+X`, as in the pointed cut derivative. -/
private def specializedComponentWeight (s : ℕ) : DeckCoeff :=
  if s = 1 then
    MvPolynomial.C 1 + MvPolynomial.X 0
  else
    MvPolynomial.C 1 + MvPolynomial.X 0 * (MvPolynomial.X 1) ^ (s - 1)

/-- The concrete deck layer obtained from the singleton-refined forest cut
polynomial by differentiating in the singleton variable and specializing it
to `1+X`; `t` is the polynomial variable and `X,Q` are its coefficients. -/
private def deckLayerPolynomial {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) : Polynomial DeckCoeff :=
  ∑ C ∈ F.edgeFinset.powerset,
    Polynomial.C ((-(1 : DeckCoeff)) ^ (F.edgeFinset.card - C.card)) *
      (Polynomial.X : Polynomial DeckCoeff) ^ C.card *
      Polynomial.C (∑ K ∈
        (componentSets (F.deleteEdges (C : Set (Sym2 V)))).filter
          (fun K => K.ncard = 1),
        ∏ J ∈
          (componentSets (F.deleteEdges (C : Set (Sym2 V)))).erase K,
          specializedComponentWeight J.ncard)

/-- Coefficient extraction of the `X Q^(s-1)` layer, leaving the deck
variable `t` as a univariate polynomial. -/
private def xqLayerCoefficient (P : Polynomial DeckCoeff) (s : ℕ) : Polynomial ℤ :=
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

private def pairBoundarySize {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (S : Finset V) (v : V) : ℕ :=
  (boundaryEdgeSet T S ∪ vertexStarEdgeSet T v).ncard

/-- Record-13 connected-pair counts, with ordered `(v,S)` pairs and the
exact boundary union `δ(S) ∪ δ(v)`. -/
private def connectedPairCount {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (s h : ℕ) : ℕ :=
  Nat.card {p : V × Finset V //
    p.2.Nonempty ∧
      p.2.card = s ∧
        p.2 ≠ (Finset.univ : Finset V) ∧
          p.1 ∉ p.2 ∧
            (T.induce (p.2 : Set V)).Connected ∧
              pairBoundarySize T p.2 p.1 = h}

private def triangularPolynomial (n s h : ℕ) : Polynomial ℤ :=
  (Polynomial.X : Polynomial ℤ) ^ h *
    (Polynomial.X - 1) ^ (n - s - h)

private def leastDegreeTriangularFamily (n s : ℕ) : Prop :=
  ∀ h : ℕ, h < n - s + 1 →
    (triangularPolynomial n s h).coeff h =
        (-1 : ℤ) ^ (n - s - h) ∧
      ∀ k : ℕ, k < h → (triangularPolynomial n s h).coeff k = 0

/-- Claim 22231: the exact deck-layer coefficient is the signed triangular
combination of the Record-13 connected-pair counts, and the nonzero least
degrees make those integer counts uniquely recoverable. -/
def claim22231_deckLayerDeterminesConnectedPairCounts : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V), T.IsTree →
    ∀ s : ℕ, 0 < s → s < Fintype.card V →
      let H : Polynomial ℤ := xqLayerCoefficient (deckLayerPolynomial T) s
      let N : ℕ → ℕ := connectedPairCount T s
      let n : ℕ := Fintype.card V
      H =
          (-1 : Polynomial ℤ) ^ (s - 1) *
            ∑ h ∈ Finset.range (n - s + 1),
              Polynomial.C (N h : ℤ) * triangularPolynomial n s h ∧
        leastDegreeTriangularFamily n s ∧
        ∀ a : ℕ → ℤ,
          H =
              (-1 : Polynomial ℤ) ^ (s - 1) *
                ∑ h ∈ Finset.range (n - s + 1),
                  Polynomial.C (a h) * triangularPolynomial n s h →
            ∀ h : ℕ, h < n - s + 1 → a h = (N h : ℤ)

end

end MathlibPlus.Open.ResearchFormalizationBatch
