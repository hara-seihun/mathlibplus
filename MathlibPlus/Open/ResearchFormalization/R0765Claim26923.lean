import Mathlib
import MathlibPlus.Open.RootedTreeBoundary
import MathlibPlus.Open.ResearchFormalizationBatch.UPolynomial

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0765

noncomputable section

open MathlibPlus.Open.RootedTreeBoundary

abbrev Coeff := MvPolynomial ℕ ℚ
abbrev RootedFactor := Polynomial Coeff

private noncomputable def componentMonomialQ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset (↥G.edgeSet)) : Coeff := by
  classical
  let H := MathlibPlus.Open.ResearchFormalizationBatch.selectedSpanningGraph G A
  letI : Finite H.ConnectedComponent :=
    Finite.of_surjective (SimpleGraph.connectedComponentMk H) (by
      intro C
      change ∃ a, Quot.mk _ a = C
      exact Quot.exists_rep C)
  letI := Fintype.ofFinite H.ConnectedComponent
  exact ∏ C : H.ConnectedComponent,
    MvPolynomial.X (MathlibPlus.Open.ResearchFormalizationBatch.selectedComponentSize G A C)

private noncomputable def rootComponentOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset (↥G.edgeSet)) (r : V) : ℕ := by
  classical
  let H := MathlibPlus.Open.ResearchFormalizationBatch.selectedSpanningGraph G A
  let C := H.connectedComponentMk r
  exact MathlibPlus.Open.ResearchFormalizationBatch.selectedComponentSize G A C

private noncomputable def rootDeletedMonomialQ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset (↥G.edgeSet)) (r : V) : Coeff := by
  classical
  let H := MathlibPlus.Open.ResearchFormalizationBatch.selectedSpanningGraph G A
  letI : Finite H.ConnectedComponent :=
    Finite.of_surjective (SimpleGraph.connectedComponentMk H) (by
      intro C
      change ∃ a, Quot.mk _ a = C
      exact Quot.exists_rep C)
  letI := Fintype.ofFinite H.ConnectedComponent
  let rootClass := H.connectedComponentMk r
  exact ∏ C : H.ConnectedComponent,
    if C = rootClass then 1
    else MvPolynomial.X
      (MathlibPlus.Open.ResearchFormalizationBatch.selectedComponentSize G A C)

private noncomputable def unrootedU
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Coeff := by
  classical
  letI : Fintype (↥G.edgeSet) := Fintype.ofFinite _
  exact ∑ A ∈ (Finset.univ : Finset (↥G.edgeSet)).powerset,
    componentMonomialQ G A

private noncomputable def deletedGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) : SimpleGraph {v : V // v ≠ r} :=
  G.induce {v | v ≠ r}

private noncomputable def rootDeletedU
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) : Coeff :=
  unrootedU (deletedGraph G r)

private noncomputable def rootedFactor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) : RootedFactor := by
  classical
  letI : Fintype (↥G.edgeSet) := Fintype.ofFinite _
  let edgeSubsets := (Finset.univ : Finset (↥G.edgeSet)).powerset
  exact edgeSubsets.sum (fun A =>
    Polynomial.C (componentMonomialQ G A) +
      Polynomial.X ^ rootComponentOrder G A r *
        Polynomial.C (rootDeletedMonomialQ G A r))

private abbrev RootedTree := MathlibPlus.Open.RootedTreeBoundary.RootedFiniteTree

private def closure (T : RootedTree) : Coeff := unrootedU T.G

private def cavity (T : RootedTree) : Coeff := rootDeletedU T.G T.root

private def factor (T : RootedTree) : RootedFactor := rootedFactor T.G T.root

private noncomputable def factorProduct
    (q : Multiset RootedTree) : RootedFactor :=
  (q.map factor).prod

private noncomputable def closureProduct
    (q : Multiset RootedTree) : Coeff :=
  (q.map closure).prod

private noncomputable def classOccurrences
    (q : Multiset RootedTree) (α : Associates Coeff) : Multiset RootedTree := by
  classical
  exact q.filter (fun T => Associates.mk (closure T) = α)

private def weightedHomogeneous (m : ℕ) (p : Coeff) : Prop :=
  ∀ e ∈ p.support,
    e.support.sum (fun j a => j * a) = m

private def monicLinearInTop (m : ℕ) (p : Coeff) : Prop :=
  ∃ a : Coeff,
    p = MvPolynomial.X m + a ∧
      ∀ e ∈ a.support, e m = 0

private def normalizedIrreducible (m : ℕ) (p : Coeff) : Prop :=
  p ≠ 0 ∧ weightedHomogeneous m p ∧ monicLinearInTop m p ∧ Irreducible p

private def matchedOrderPureCore
    (m : ℕ) (c : Fin 3 → ℚ)
    (q : Fin 3 → Multiset RootedTree) : Prop :=
  (∀ i, c i ≠ 0) ∧
    (∑ i : Fin 3, c i = 0) ∧
    (∀ i T, T ∈ q i → Fintype.card T.V = m) ∧
    (∀ i T, T ∈ q i → normalizedIrreducible m (closure T)) ∧
    (∀ i j, i ≠ j → IsCoprime (factorProduct (q i)) (factorProduct (q j))) ∧
    (∀ i, closureProduct (q i) = closureProduct (q 0)) ∧
    (∑ i : Fin 3,
      Polynomial.C (MvPolynomial.C (c i)) * factorProduct (q i) = 0)

/-- Claim 26923: in an actual matched rooted-tree core, a class with one
occurrence in each product has the same additive and multiplicative cavity
balance.  The class is represented by the normalized associate of the actual
unrooted U-polynomial, and occurrences retain the actual rooted trees. -/
def singletonClassCoincidence_claim26923 : Prop :=
  ∀ (m : ℕ) (c : Fin 3 → ℚ)
    (q : Fin 3 → Multiset RootedTree) (α : Associates Coeff),
    matchedOrderPureCore m c q →
    (∀ i, (classOccurrences (q i) α).card = 1) →
    (∀ i, ((classOccurrences (q i) α).map cavity).sum =
      ((classOccurrences (q i) α).map cavity).prod) ∧
    (∑ i : Fin 3, MvPolynomial.C (c i) *
      ((classOccurrences (q i) α).map cavity).sum = 0) ∧
    (∑ i : Fin 3, MvPolynomial.C (c i) *
      ((classOccurrences (q i) α).map cavity).prod = 0)

end

end MathlibPlus.Open.ResearchFormalization.R0765
