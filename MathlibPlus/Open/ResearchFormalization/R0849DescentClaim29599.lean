import Mathlib
import MathlibPlus.Open.ResearchFormalization.R0849

namespace MathlibPlus.Open.ResearchFormalization.R0849DescentClaim29599

open Classical
open scoped BigOperators
noncomputable section

abbrev SourcePolynomial := MvPolynomial ℕ ℚ

/-- The finite edge universe of a finite simple graph. -/
def uEdgeUniverse {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) : Finset (Sym2 V) :=
  F.edgeSet.toFinite.toFinset

def uReachable {V : Type*}
    (E : Finset (Sym2 V)) (u v : V) : Prop :=
  Relation.ReflTransGen (fun x y : V => Sym2.mk x y ∈ E) u v

def uComponent {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (v : V) : Finset V :=
  Finset.univ.filter (uReachable E v)

def uComponents {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) : Finset (Finset V) :=
  Finset.univ.image (uComponent E)

/-- The ordinary forest U-polynomial, written as the edge-subset/component
sum used by the connected-packing filtration. -/
noncomputable def forestUPolynomial {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) : SourcePolynomial :=
  ∑ E ∈ (uEdgeUniverse F).powerset,
    ∏ C ∈ uComponents E, MvPolynomial.X C.card

noncomputable def packingRow {V : Type*} [Fintype V] [DecidableEq V]
    (F : Fin 4 → SimpleGraph V) (r : ℕ) (i : Fin 4) : SourcePolynomial :=
  MathlibPlus.Open.ResearchFormalization.R0849.connectedPackingCoefficient (F i) r

def rowsAllEqualAt {V : Type*} [Fintype V] [DecidableEq V]
    (F : Fin 4 → SimpleGraph V) (r : ℕ) : Prop :=
  ∀ i : Fin 4, packingRow F r i = packingRow F r 0

def rowsAllDistinctAt {V : Type*} [Fintype V] [DecidableEq V]
    (F : Fin 4 → SimpleGraph V) (r : ℕ) : Prop :=
  ∀ ⦃i j : Fin 4⦄, i ≠ j → packingRow F r i ≠ packingRow F r j

/-- Pairwise distinctness of exactly the three entries that split in the
affine branch.  The fourth entry is intentionally not constrained. -/
def tripleRowsDistinctAt {V : Type*} [Fintype V] [DecidableEq V]
    (F : Fin 4 → SimpleGraph V) (r : ℕ) : Prop :=
  packingRow F r 0 ≠ packingRow F r 1 ∧
    packingRow F r 0 ≠ packingRow F r 2 ∧
    packingRow F r 1 ≠ packingRow F r 2

def firstPositivePackingSplit {V : Type*} [Fintype V] [DecidableEq V]
    (F : Fin 4 → SimpleGraph V) (h : ℕ) : Prop :=
  0 < h ∧ ¬ rowsAllEqualAt F h ∧
    ∀ r : ℕ, 0 < r → r < h → rowsAllEqualAt F r

def pairwiseDistinctForestUPolynomials
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : Fin 4 → SimpleGraph V) : Prop :=
  ∀ ⦃i j : Fin 4⦄, i ≠ j →
    forestUPolynomial (F i) ≠ forestUPolynomial (F j)

def sourceCrossRatio {V : Type*} [Fintype V] [DecidableEq V]
    (F : Fin 4 → SimpleGraph V) (lam : ℚ) : Prop :=
  (forestUPolynomial (F 0) - forestUPolynomial (F 3)) *
      (forestUPolynomial (F 1) - forestUPolynomial (F 2)) =
    MvPolynomial.C lam *
      ((forestUPolynomial (F 0) - forestUPolynomial (F 2)) *
        (forestUPolynomial (F 1) - forestUPolynomial (F 3)))

def packingCrossRatio {V : Type*} [Fintype V] [DecidableEq V]
    (F : Fin 4 → SimpleGraph V) (lam : ℚ) (h : ℕ) : Prop :=
  (packingRow F h 0 - packingRow F h 3) *
      (packingRow F h 1 - packingRow F h 2) =
    MvPolynomial.C lam *
      ((packingRow F h 0 - packingRow F h 2) *
        (packingRow F h 1 - packingRow F h 3))

def anharmonicTransform (mu lam : ℚ) : Prop :=
  mu = lam ∨ mu = 1 - lam ∨ mu = 1 / lam ∨ mu = 1 / (1 - lam) ∨
    mu = lam / (lam - 1) ∨ mu = (lam - 1) / lam

/-- The first delayed row at which the three equal entries stop being all
 equal.  Pairwise distinctness is deliberately a conclusion of the descent,
not part of this predicate. -/
def firstTripleSplit {V : Type*} [Fintype V] [DecidableEq V]
    (F : Fin 4 → SimpleGraph V) (h k : ℕ) : Prop :=
  packingRow F h 0 = packingRow F h 1 ∧
    packingRow F h 1 = packingRow F h 2 ∧
    h < k ∧
    (∀ r : ℕ, h < r → r < k →
      packingRow F r 0 = packingRow F r 1 ∧
        packingRow F r 1 = packingRow F r 2) ∧
    ¬ (packingRow F k 0 = packingRow F k 1 ∧
      packingRow F k 1 = packingRow F k 2)

def affineTripleAt {V : Type*} [Fintype V] [DecidableEq V]
    (F : Fin 4 → SimpleGraph V) (k : ℕ) (mu : ℚ) : Prop :=
  packingRow F k 1 - packingRow F k 2 =
    MvPolynomial.C mu * (packingRow F k 0 - packingRow F k 2)

def relabelRows {V : Type*} [Fintype V] [DecidableEq V]
    (F : Fin 4 → SimpleGraph V) (σ : Equiv.Perm (Fin 4)) :
    Fin 4 → SimpleGraph V :=
  fun i => F (σ i)

/-- Claim 29599: a nontrivial rational cross ratio of four distinct
common-order forest U-polynomials descends to a connected-packing
cross-ratio row or to the delayed rational affine triple, and every output
row has strictly smaller x-degree. -/
def claim29599_connectedPackingDescentDichotomy : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (F : Fin 4 → SimpleGraph V),
    (∀ i : Fin 4, (F i).IsAcyclic) →
    pairwiseDistinctForestUPolynomials F →
    ∀ lam : ℚ, lam ≠ 0 → lam ≠ 1 → sourceCrossRatio F lam →
      ∃ h : ℕ,
        firstPositivePackingSplit F h ∧
        ((rowsAllDistinctAt F h ∧
            packingCrossRatio F lam h ∧
            ∀ i : Fin 4,
              MvPolynomial.degreeOf 0 (packingRow F h i) < Fintype.card V) ∨
          (∃ σ : Equiv.Perm (Fin 4),
            let F' := relabelRows F σ
            packingRow F' h 0 = packingRow F' h 1 ∧
              packingRow F' h 1 = packingRow F' h 2 ∧
              packingRow F' h 0 ≠ packingRow F' h 3 ∧
              ∃ k : ℕ, ∃ mu : ℚ,
                firstTripleSplit F' h k ∧
                tripleRowsDistinctAt F' k ∧
                anharmonicTransform mu lam ∧ mu ≠ 0 ∧ mu ≠ 1 ∧
                affineTripleAt F' k mu ∧
                ∀ i : Fin 4,
                  MvPolynomial.degreeOf 0 (packingRow F' k i) <
                    Fintype.card V))

end
end MathlibPlus.Open.ResearchFormalization.R0849DescentClaim29599
