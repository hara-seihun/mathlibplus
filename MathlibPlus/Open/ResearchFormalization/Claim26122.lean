import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch019ffedf141b77c7b96e46e312eadae9

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Claim26122

open MathlibPlus.Open.ResearchFormalizationBatch

structure LegFamily where
  count : ℕ
  length : Fin count → ℕ

private def positiveLegFamily (A : LegFamily) : Prop :=
  ∀ i, 0 < A.length i

private def legSum (A : LegFamily) : ℕ :=
  ∑ i : Fin A.count, A.length i

private def legMultiset (A : LegFamily) : Multiset ℕ :=
  (Finset.univ : Finset (Fin A.count)).val.map A.length

structure DoubleSpider where
  smaller : LegFamily
  trunk : ℕ
  larger : LegFamily

private def validDoubleSpider (T : DoubleSpider) : Prop :=
  positiveLegFamily T.smaller ∧
    positiveLegFamily T.larger ∧
    2 ≤ T.smaller.count ∧ 2 ≤ T.larger.count ∧ 1 ≤ T.trunk

private abbrev LegVertex (A : LegFamily) :=
  Σ i : Fin A.count, Fin (A.length i)

private def legAdjacent {A : LegFamily}
    (x y : LegVertex A) : Prop :=
  x.1 = y.1 ∧
    (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)

private abbrev SpiderVertex (A B : LegFamily) (c : ℕ) :=
  Fin (c + 1) ⊕ (LegVertex A ⊕ LegVertex B)

private def doubleSpiderRelation (A B : LegFamily) (c : ℕ)
    (u v : SpiderVertex A B c) : Prop :=
  match u, v with
  | Sum.inl r, Sum.inl s => r.val + 1 = s.val
  | Sum.inl r, Sum.inr (Sum.inl x) => r.val = 0 ∧ x.2.val = 0
  | Sum.inr (Sum.inl x), Sum.inl r => r.val = 0 ∧ x.2.val = 0
  | Sum.inl r, Sum.inr (Sum.inr x) => r.val = c ∧ x.2.val = 0
  | Sum.inr (Sum.inr x), Sum.inl r => r.val = c ∧ x.2.val = 0
  | Sum.inr (Sum.inl x), Sum.inr (Sum.inl y) => legAdjacent x y
  | Sum.inr (Sum.inr x), Sum.inr (Sum.inr y) => legAdjacent x y
  | _, _ => False

private def doubleSpiderGraph (A B : LegFamily) (c : ℕ) :
    SimpleGraph (SpiderVertex A B c) :=
  SimpleGraph.fromRel (doubleSpiderRelation A B c)

private abbrev SingleSpiderVertex (A : LegFamily) :=
  Unit ⊕ LegVertex A

private def singleSpiderRelation (A : LegFamily)
    (u v : SingleSpiderVertex A) : Prop :=
  match u, v with
  | Sum.inl _, Sum.inr x => x.2.val = 0
  | Sum.inr x, Sum.inl _ => x.2.val = 0
  | Sum.inr x, Sum.inr y => legAdjacent x y
  | _, _ => False

private def singleSpiderGraph (A : LegFamily) :
    SimpleGraph (SingleSpiderVertex A) :=
  SimpleGraph.fromRel (singleSpiderRelation A)

private def pathGraph (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v : Fin n => u.val + 1 = v.val)

private noncomputable def spiderU {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : MvPolynomial ℕ ℚ :=
  unsignedConnectedSetPolynomial G

private noncomputable def spiderM {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : MvPolynomial ℕ ℚ :=
  markedSingletonPolynomial G

private noncomputable def doubleU (T : DoubleSpider) : MvPolynomial ℕ ℚ :=
  spiderU (doubleSpiderGraph T.smaller T.larger T.trunk)

private noncomputable def doubleM (T : DoubleSpider) : MvPolynomial ℕ ℚ :=
  spiderM (doubleSpiderGraph T.smaller T.larger T.trunk)

private noncomputable def singleU (A : LegFamily) : MvPolynomial ℕ ℚ :=
  spiderU (singleSpiderGraph A)

private noncomputable def singleM (A : LegFamily) : MvPolynomial ℕ ℚ :=
  spiderM (singleSpiderGraph A)

private noncomputable def pathU (n : ℕ) : MvPolynomial ℕ ℚ :=
  spiderU (pathGraph n)

private noncomputable def pathM (n : ℕ) : MvPolynomial ℕ ℚ :=
  spiderM (pathGraph n)

private def unitAugmented (A : LegFamily) : LegFamily :=
  { count := A.count + 1
    length := fun i =>
      if h : i.val < A.count then A.length ⟨i.val, h⟩ else 1 }

private noncomputable def trunkEdges (T : DoubleSpider) :
    Finset (Sym2 (SpiderVertex T.smaller T.larger T.trunk)) :=
  (Finset.univ : Finset (Fin T.trunk)).image (fun i =>
    s((Sum.inl (Fin.castSucc i) : SpiderVertex T.smaller T.larger T.trunk),
      (Sum.inl (Fin.succ i) : SpiderVertex T.smaller T.larger T.trunk)))

private noncomputable def noTrunkCutU (T : DoubleSpider) :
    MvPolynomial ℕ ℚ := by
  classical
  let G := doubleSpiderGraph T.smaller T.larger T.trunk
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  exact ∑ E₀ ∈ G.edgeFinset.powerset,
    if trunkEdges T ⊆ E₀ then componentMonomial E₀ else 0

private noncomputable def crossedU (T : DoubleSpider) : MvPolynomial ℕ ℚ :=
  doubleU T - noTrunkCutU T

private noncomputable def crossedM (T : DoubleSpider) : MvPolynomial ℕ ℚ :=
  partialOne (crossedU T)

private def rootSideRelation (A : LegFamily) (i : ℕ)
    (u v : Fin (i + 1) ⊕ LegVertex A) : Prop :=
  match u, v with
  | Sum.inl r, Sum.inl s => r.val + 1 = s.val
  | Sum.inl r, Sum.inr x => r.val = 0 ∧ x.2.val = 0
  | Sum.inr x, Sum.inl r => r.val = 0 ∧ x.2.val = 0
  | Sum.inr x, Sum.inr y => legAdjacent x y

private def rootSideGraph (A : LegFamily) (i : ℕ) :
    SimpleGraph (Fin (i + 1) ⊕ LegVertex A) :=
  SimpleGraph.fromRel (rootSideRelation A i)

private noncomputable def rootSideU (A : LegFamily) (i : ℕ) :
    MvPolynomial ℕ ℚ :=
  spiderU (rootSideGraph A i)

private noncomputable def crossedFactorizedU (T : DoubleSpider) :
    MvPolynomial ℕ ℚ :=
  ∑ i ∈ Finset.range T.trunk,
    ∑ j ∈ Finset.range T.trunk,
      ∑ h ∈ Finset.range T.trunk,
        if i + j + h = T.trunk - 1 then
          rootSideU T.smaller i * pathU h * rootSideU T.larger j
        else 0

private noncomputable def componentCoefficient (k : ℕ)
    (P : MvPolynomial ℕ ℚ) : MvPolynomial ℕ ℚ :=
  ∑ d ∈ P.support.filter (fun d => d k ≠ 0),
    MvPolynomial.monomial (d - Finsupp.single k 1)
      (P.coeff d * (d k : ℚ))

private noncomputable def xOne : MvPolynomial ℕ ℚ :=
  MvPolynomial.X 1

private def sameReconstruction (T T' : DoubleSpider) : Prop :=
  validDoubleSpider T ∧
    validDoubleSpider T' ∧
    T.smaller.count = 2 ∧ T'.smaller.count = 2 ∧
    legSum T.smaller = legSum T'.smaller ∧
    legMultiset T.smaller + legMultiset T.larger =
      legMultiset T'.smaller + legMultiset T'.larger ∧
    T.trunk = T'.trunk ∧
    legSum T.smaller < legSum T.larger ∧
    legSum T'.smaller < legSum T'.larger

/-- Claim 26122: after the known smaller-side sum, trunk, and global leg
    multiset have been reconstructed, the three easy residual cases retain
    their exact factorization, coefficient correction, and recovery step. -/
def sideAssignmentEasyResidualCases_claim26122 : Prop :=
  ∀ (T T' : DoubleSpider),
    sameReconstruction T T' →
    (T.larger.count = 2 →
      legMultiset T.smaller = legMultiset T'.smaller ∧
        legMultiset T.larger = legMultiset T'.larger) ∧
    (T.trunk = 1 →
      crossedU T =
          pathU (legSum T.smaller + 1) * singleU T.larger ∧
      crossedU T' =
          pathU (legSum T'.smaller + 1) * singleU T'.larger ∧
      (crossedM T = crossedM T' →
        legMultiset T.larger = legMultiset T'.larger)) ∧
    (2 ≤ T.trunk → legSum T.larger ≥ legSum T.smaller + 2 →
      let α := legSum T.smaller
      let β := legSum T.larger
      let q := T.larger.count
      componentCoefficient (β + T.trunk - 1) (crossedM T) =
          singleM (unitAugmented T.smaller) +
            (q : ℚ) •
              (pathU (α + 1) + xOne * pathM (α + 1)) ∧
        (componentCoefficient (β + T.trunk - 1) (crossedM T) =
            componentCoefficient (β + T'.trunk - 1) (crossedM T') →
          singleM (unitAugmented T.smaller) =
              singleM (unitAugmented T'.smaller) ∧
            legMultiset T.smaller = legMultiset T'.smaller))

end MathlibPlus.Open.ResearchFormalization.Claim26122
