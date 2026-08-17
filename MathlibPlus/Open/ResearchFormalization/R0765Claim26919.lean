import MathlibPlus.Open.RootedTreeBoundary
import MathlibPlus.Open.ResearchFormalizationBatch.UPolynomial

open scoped BigOperators
open Classical
attribute [local instance] Classical.propDecidable Classical.decEq

namespace MathlibPlus.Open.ResearchFormalization.R0765Claim26919

noncomputable section

open MathlibPlus.Open.RootedTreeBoundary

abbrev Coeff := MvPolynomial ℕ ℚ
abbrev RootedFactor := Polynomial Coeff
abbrev RootedTree := MathlibPlus.Open.RootedTreeBoundary.RootedFiniteTree

def componentMonomialQ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset (↥G.edgeSet)) : Coeff :=
  let H := MathlibPlus.Open.ResearchFormalizationBatch.selectedSpanningGraph G A
  letI : Finite H.ConnectedComponent :=
    Finite.of_surjective (SimpleGraph.connectedComponentMk H)
      (fun C => Quot.exists_rep C)
  letI := Fintype.ofFinite H.ConnectedComponent
  ∏ C : H.ConnectedComponent,
    MvPolynomial.X
      (MathlibPlus.Open.ResearchFormalizationBatch.selectedComponentSize G A C)

def rootComponentOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset (↥G.edgeSet)) (r : V) : ℕ :=
  let H := MathlibPlus.Open.ResearchFormalizationBatch.selectedSpanningGraph G A
  let C := H.connectedComponentMk r
  MathlibPlus.Open.ResearchFormalizationBatch.selectedComponentSize G A C

def rootDeletedMonomialQ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset (↥G.edgeSet)) (r : V) : Coeff :=
  let H := MathlibPlus.Open.ResearchFormalizationBatch.selectedSpanningGraph G A
  letI : Finite H.ConnectedComponent :=
    Finite.of_surjective (SimpleGraph.connectedComponentMk H)
      (fun C => Quot.exists_rep C)
  letI := Fintype.ofFinite H.ConnectedComponent
  let rootClass := H.connectedComponentMk r
  ∏ C : H.ConnectedComponent,
    if C = rootClass then 1 else
      MvPolynomial.X
        (MathlibPlus.Open.ResearchFormalizationBatch.selectedComponentSize G A C)

def unrootedU
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Coeff :=
  letI : Fintype (↥G.edgeSet) := Fintype.ofFinite _
  ∑ A ∈ (Finset.univ : Finset (↥G.edgeSet)).powerset,
    componentMonomialQ G A

def deletedGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) : SimpleGraph {v : V // v ≠ r} :=
  G.induce {v | v ≠ r}

def rootDeletedU
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) : Coeff :=
  unrootedU (deletedGraph G r)

def rootedFactor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) : RootedFactor :=
  letI : Fintype (↥G.edgeSet) := Fintype.ofFinite _
  let edgeSubsets := (Finset.univ : Finset (↥G.edgeSet)).powerset
  edgeSubsets.sum (fun A =>
    Polynomial.C (componentMonomialQ G A) +
      Polynomial.X ^ rootComponentOrder G A r *
        Polynomial.C (rootDeletedMonomialQ G A r))

def closure (T : RootedTree) : Coeff := unrootedU T.G

def cavity (T : RootedTree) : Coeff := rootDeletedU T.G T.root

def factor (T : RootedTree) : RootedFactor := rootedFactor T.G T.root

def factorProduct (q : Multiset RootedTree) : RootedFactor :=
  (q.map factor).prod

def closureProduct (q : Multiset RootedTree) : Coeff :=
  (q.map closure).prod

def classOccurrences (q : Multiset RootedTree)
    (α : Associates Coeff) : Multiset RootedTree :=
  q.filter (fun T => Associates.mk (closure T) = α)

def normalizedIrreducible (m : ℕ) (p : Coeff) : Prop :=
  p ≠ 0 ∧
    (∀ e ∈ p.support, e.support.sum (fun j a => j * a) = m) ∧
    (∃ a : Coeff,
      p = MvPolynomial.X m + a ∧
        ∀ e ∈ a.support, e m = 0) ∧
    Irreducible p

def matchedOrderPureCore
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

def classMultiplicity (q : Multiset RootedTree)
    (α : Associates Coeff) : ℕ :=
  (classOccurrences q α).card

/-- Unique factorization of the common actual U-polynomial closure, with the
positive multiplicity of each normalized irreducible class equal to the number
of actual rooted factors in every one of the three products. -/
def claim26919 : Prop :=
  ∀ (m : ℕ) (c : Fin 3 → ℚ)
    (q : Fin 3 → Multiset RootedTree),
    matchedOrderPureCore m c q →
      ∃ (s : ℕ) (U : Fin s → Associates Coeff)
        (d : Fin s → ℕ),
        Function.Injective U ∧
          (∀ a : Fin s, 0 < d a) ∧
            (∀ i : Fin 3, ∀ a : Fin s,
              classMultiplicity (q i) (U a) = d a) ∧
              (∀ i : Fin 3, ∀ α : Associates Coeff,
                ((∃ a : Fin s, U a = α) ↔
                  0 < classMultiplicity (q i) α)) ∧
                Associates.mk (closureProduct (q 0)) =
                  ∏ a : Fin s, U a ^ d a

end

end MathlibPlus.Open.ResearchFormalization.R0765Claim26919
