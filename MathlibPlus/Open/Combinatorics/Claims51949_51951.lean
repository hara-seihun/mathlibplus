import Mathlib
import MathlibPlus.Open.Combinatorics.DTreeUPolynomial

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics.StanleyAugmentation

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev TreePolynomial := MvPolynomial ℕ ℤ

/-- The finite edge set of a finite simple graph. -/
def ordinaryGraphEdges {V : Type*} [Fintype V]
    (T : SimpleGraph V) : Finset (Sym2 V) :=
  Finset.univ.filter (fun e : Sym2 V => e ∈ T.edgeSet)

/-- A subset of the edge set, interpreted as the deleted edges. -/
def ordinaryEdgeSubset {V : Type*} [Fintype V]
    (T : SimpleGraph V) :=
  {S : Finset (Sym2 V) // S ⊆ ordinaryGraphEdges T}

/-- The component partition after deleting an edge subset. -/
def ordinaryPartitionFromCut {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : ordinaryEdgeSubset T) : Setoid V :=
  Relation.EqvGen.setoid (fun a b : V =>
    T.Adj a b ∧ s(a, b) ∉ S.1)

/-- The component-size monomial attached to a finite partition. -/
def ordinaryComponentMonomial {V : Type*} [Fintype V]
    (p : Setoid V) : TreePolynomial :=
  ∏ q : Quotient p,
    MvPolynomial.X (Fintype.card {v : V // Quotient.mk' v = q})

/-- The ordinary isomorphism-invariant edge-subset/component-size
U-polynomial.  No auxiliary order on the vertex carrier is used. -/
def treeU {V : Type*} [Fintype V]
    (T : SimpleGraph V) : TreePolynomial :=
  letI : Fintype (ordinaryEdgeSubset T) := Subtype.fintype _
  (Finset.univ : Finset (ordinaryEdgeSubset T)).sum (fun S =>
    ordinaryComponentMonomial (ordinaryPartitionFromCut T S))

/-- The U-polynomial of the one-leaf augmentation at a specified vertex
occurrence. -/
def augmentationValue {V : Type*} [Fintype V]
    (T : SimpleGraph V) (v : V) : TreePolynomial :=
  treeU
    (MathlibPlus.Open.Combinatorics.DTreeUPolynomial.leafExtension T v)

/-- The disjoint forest of one-leaf augmentations indexed by distinct vertex
occurrences in `S`. -/
def augmentationForest {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) :
    SimpleGraph (↥S × Option V) :=
  SimpleGraph.fromRel (fun x y =>
    x.1 = y.1 ∧
      (MathlibPlus.Open.Combinatorics.DTreeUPolynomial.leafExtension T
        (x.1 : V)).Adj x.2 y.2)

/-- The U-image of that disjoint augmentation forest. -/
def forestU {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) : TreePolynomial :=
  treeU (augmentationForest T S)

/-- One elementary summand, retaining the multiplicity of each vertex
occurrence. -/
def elementarySummand {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) : TreePolynomial :=
  ∏ v ∈ S, augmentationValue T v

/-- The elementary coefficient formed from distinct vertex occurrences. -/
def elementaryCoefficient {V : Type*} [Fintype V]
    (T : SimpleGraph V) (r : ℕ) : TreePolynomial :=
  ∑ S : Finset V,
    if S.card = r then elementarySummand T S else 0

/-- The augmentation-root polynomial with repeated orbit values repeated by
occurrence multiplicity. -/
def augmentationLambda {V : Type*} [Fintype V]
    (T : SimpleGraph V) : Polynomial TreePolynomial :=
  ∏ v : V,
    ((Polynomial.X : Polynomial TreePolynomial) -
      Polynomial.C (augmentationValue T v))

/-- The augmentation power moment. -/
def powerMoment {V : Type*} [Fintype V]
    (T : SimpleGraph V) (j : ℕ) : TreePolynomial :=
  ∑ v : V, (augmentationValue T v) ^ j

/-- Claim 51949: distinct monic augmentation-root polynomials with equal first
coefficient have a least separating elementary degree, and each summand there
is the U-image of the forest of the corresponding distinct augmentations. -/
def firstSeparatingElementaryCoefficient_claim51949 : Prop :=
  ∀ {V W : Type*} [Fintype V] [Fintype W]
    (T : SimpleGraph V) (T' : SimpleGraph W) (n : ℕ),
    T.IsTree →
    T'.IsTree →
    Fintype.card V = n →
    Fintype.card W = n →
    ¬ Nonempty (T ≃g T') →
    treeU T = treeU T' →
    (augmentationLambda T).Monic ∧
      (augmentationLambda T').Monic ∧
      (augmentationLambda T).natDegree = n ∧
      (augmentationLambda T').natDegree = n ∧
      augmentationLambda T ≠ augmentationLambda T' ∧
      elementaryCoefficient T 1 = elementaryCoefficient T' 1 ∧
      ∃ r : ℕ,
        2 ≤ r ∧
        r ≤ n ∧
        elementaryCoefficient T r ≠ elementaryCoefficient T' r ∧
        (∀ j : ℕ, 2 ≤ j → j < r →
          elementaryCoefficient T j = elementaryCoefficient T' j) ∧
        (∀ S : Finset V, S.card = r →
          elementarySummand T S = forestU T S) ∧
        (∀ S : Finset W, S.card = r →
          elementarySummand T' S = forestU T' S)

/-- Claim 51951: Newton power sums separate the same pair at its least
separating elementary degree, with the exact sign and multiplicity factor. -/
def powerMomentSeparation_claim51951 : Prop :=
  ∀ {V W : Type*} [Fintype V] [Fintype W]
    (T : SimpleGraph V) (T' : SimpleGraph W) (n : ℕ),
    T.IsTree →
    T'.IsTree →
    Fintype.card V = n →
    Fintype.card W = n →
    ¬ Nonempty (T ≃g T') →
    treeU T = treeU T' →
    elementaryCoefficient T 1 = elementaryCoefficient T' 1 ∧
      ∃ r : ℕ,
        2 ≤ r ∧
        r ≤ n ∧
        elementaryCoefficient T r ≠ elementaryCoefficient T' r ∧
        (∀ j : ℕ, 2 ≤ j → j < r →
          elementaryCoefficient T j = elementaryCoefficient T' j) ∧
        (∀ j : ℕ, 1 ≤ j → j < r →
          powerMoment T j = powerMoment T' j) ∧
        powerMoment T r - powerMoment T' r =
          (-1 : TreePolynomial) ^ (r + 1) *
            (r : TreePolynomial) *
            (elementaryCoefficient T r - elementaryCoefficient T' r) ∧
        powerMoment T r - powerMoment T' r ≠ 0 ∧
        powerMoment T r ≠ powerMoment T' r ∧
      ∃ r : ℕ,
        2 ≤ r ∧ r ≤ n ∧ powerMoment T r ≠ powerMoment T' r

end

end MathlibPlus.Open.Combinatorics.StanleyAugmentation
