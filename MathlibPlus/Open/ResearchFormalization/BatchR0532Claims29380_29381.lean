import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchR0532

open scoped BigOperators
noncomputable section

abbrev BivariatePoly := MvPolynomial (Fin 2) ℤ

def uVar : BivariatePoly := MvPolynomial.X 0
def zVar : BivariatePoly := MvPolynomial.X 1

def bivariateConst (n : ℕ) : BivariatePoly := MvPolynomial.C (n : ℤ)
def integerConst (n : ℤ) : Polynomial ℤ := Polynomial.C n

/-- The q-integer `[a]_u` and its product over a leg multiset. -/
def qIntegerZ (a : ℕ) : Polynomial ℤ :=
  ∑ j ∈ Finset.range a, (Polynomial.X : Polynomial ℤ) ^ j

def sideQProduct (s : Multiset ℕ) : Polynomial ℤ :=
  (s.map qIntegerZ).prod

/-- The top marked one-leg coefficient used by the adjacent `2`-by-`r`
 grouping functional. -/
def markedLegTop (a : ℕ) : Polynomial ℤ :=
  ∑ j ∈ Finset.range a,
    integerConst ((a - j - 2 : ℕ) : ℤ) * (Polynomial.X : Polynomial ℤ) ^ j

def markedGlobalProduct (s : Multiset ℕ) : Polynomial ℤ :=
  (s.map (fun a => markedLegTop a * sideQProduct (s.erase a))).sum

def tailSum (s : Multiset ℕ) : Polynomial ℤ :=
  (s.map (fun a => qIntegerZ a - 1)).sum

/-- The exact exceptional adjacent grouping functional from the retained
`z^(r+2)` grade. -/
def exceptionalGroupingFunctional
    (N : ℕ) (large small : Multiset ℕ) : Polynomial ℤ :=
  (Polynomial.X * markedGlobalProduct large) +
    (Polynomial.X *
      (integerConst ((N : ℤ) - 1) * sideQProduct large +
        sideQProduct small)) -
    tailSum large

/-- Parameter data for `T(A,c,B)`: `c` is the number of trunk edges and the
 two multisets retain repeated pendant-leg lengths. -/
structure DoubleSpiderParameters where
  left : Multiset ℕ
  trunk : ℕ
  right : Multiset ℕ

abbrev DoubleSpider := DoubleSpiderParameters

def positiveLegs (s : Multiset ℕ) : Prop :=
  ∀ a, a ∈ s → 0 < a

def admissibleDoubleSpider (T : DoubleSpider) : Prop :=
  0 < T.trunk ∧
    positiveLegs T.left ∧ positiveLegs T.right ∧
    2 ≤ T.left.card ∧ 2 ≤ T.right.card

def equalTotalDoubleSpider (T : DoubleSpider) : Prop :=
  admissibleDoubleSpider T ∧ T.left.sum = T.right.sum

def sideTotal (T : DoubleSpider) : ℕ := T.left.sum

def globalLegMultiset (T : DoubleSpider) : Multiset ℕ :=
  T.left + T.right

def doubleSpiderOrder (T : DoubleSpider) : ℕ :=
  T.trunk + 1 + T.left.sum + T.right.sum

def sideExchangeEquivalent
    (T T' : DoubleSpider) : Prop :=
  T.trunk = T'.trunk ∧
    ((T.left = T'.left ∧ T.right = T'.right) ∨
      (T.left = T'.right ∧ T.right = T'.left))

/-- The four exhaustive predicates, with the last one symmetric under side
exchange. -/
def caseLongTrunk (T : DoubleSpider) : Prop :=
  2 ≤ T.trunk

def caseAdjacentAtLeastThree (T : DoubleSpider) : Prop :=
  T.trunk = 1 ∧ 3 ≤ T.left.card ∧ 3 ≤ T.right.card

def caseAdjacentTwoByTwo (T : DoubleSpider) : Prop :=
  T.trunk = 1 ∧ T.left.card = 2 ∧ T.right.card = 2

def caseAdjacentTwoByR (T : DoubleSpider) : Prop :=
  T.trunk = 1 ∧
    ((T.left.card = 2 ∧ 3 ≤ T.right.card) ∨
      (T.right.card = 2 ∧ 3 ≤ T.left.card))

/-- A fixed `(U,N,r,2)` admissible grouping of the two sides. -/
def admissibleTwoByRGrouping
    (U : Multiset ℕ) (N r : ℕ)
    (large small : Multiset ℕ) : Prop :=
  3 ≤ r ∧
    positiveLegs large ∧ positiveLegs small ∧
    large.card = r ∧ small.card = 2 ∧
    large + small = U ∧
    large.sum = N ∧ small.sum = N

/-- Claim 29380: at fixed recovered global multiset, common side total, and
counts `r,2`, the exceptional grouping value is injective on the exact
admissible side-grouping carrier. -/
def injectiveAdjacentTwoByRGrouping_claim29380 : Prop :=
  ∀ (U : Multiset ℕ) (N r : ℕ)
    (large small large' small' : Multiset ℕ),
    admissibleTwoByRGrouping U N r large small →
      admissibleTwoByRGrouping U N r large' small' →
      exceptionalGroupingFunctional N large small =
        exceptionalGroupingFunctional N large' small' →
      large = large' ∧
        ((large = large' ∧ small = small') ∨
          (large = small' ∧ small = large'))

/-- The exact side-pair data supplied by the nonadjacent and the
adjacent-at-least-three boundary identities. -/
structure SideBoundaryData where
  trunk : ℕ
  total : ℕ
  global : Multiset ℕ
  sideProductSum : Polynomial ℤ

def sideBoundaryData (T : DoubleSpider) : SideBoundaryData :=
  { trunk := T.trunk
    total := sideTotal T
    global := globalLegMultiset T
    sideProductSum := sideQProduct T.left + sideQProduct T.right }

/-- The orientation used in the exceptional case is determined by the side
count, since `r ≥ 3` and the other side has count two. -/
def largeSide (T : DoubleSpider) : Multiset ℕ :=
  if T.left.card > T.right.card then T.left else T.right

def smallSide (T : DoubleSpider) : Multiset ℕ :=
  if T.left.card > T.right.card then T.right else T.left

def exceptionalData (T : DoubleSpider) :
    ℕ × ℕ × Multiset ℕ × ℕ × Polynomial ℤ :=
  (T.trunk, sideTotal T, globalLegMultiset T, (largeSide T).card,
    exceptionalGroupingFunctional (sideTotal T) (largeSide T) (smallSide T))

/-- Exact one-leg factors in the two-variable one-hole transform. -/
def legFactor (a : ℕ) : BivariatePoly :=
  uVar ^ a + zVar * (∑ j ∈ Finset.range a, uVar ^ j)

def pathDegree (length : ℕ) : BivariatePoly :=
  if length = 1 then 1
  else 2 * zVar + bivariateConst (length - 2) * zVar ^ 2

def markedLegFactor (a : ℕ) : BivariatePoly :=
  uVar ^ (a - 1) +
    ∑ pfx ∈ Finset.range (a - 1),
      uVar ^ pfx * pathDegree (a - pfx)

def sideProduct (s : Multiset ℕ) : BivariatePoly :=
  (s.map legFactor).prod

def markedSideProduct (s : Multiset ℕ) : BivariatePoly :=
  (s.map (fun a => markedLegFactor a * sideProduct (s.erase a))).sum

def degreePolynomial (T : DoubleSpider) : BivariatePoly :=
  let leaves := T.left.card + T.right.card
  let order := doubleSpiderOrder T
  let degreeTwo := order - leaves - 2
  bivariateConst leaves * zVar +
      bivariateConst degreeTwo * zVar ^ 2 +
      zVar ^ (T.left.card + 1) + zVar ^ (T.right.card + 1)

def extendedSideDegree
    (total count extension : ℕ) : BivariatePoly :=
  if extension = 0 then
    zVar ^ count + bivariateConst count * zVar +
      bivariateConst (total - count) * zVar ^ 2
  else
    zVar ^ (count + 1) + bivariateConst (count + 1) * zVar +
      bivariateConst (total - count + extension - 1) * zVar ^ 2

def oneCenterFormula
    (side : Multiset ℕ) (trunk : ℕ) (opposite : Multiset ℕ) : BivariatePoly :=
  uVar * zVar *
      (∑ j ∈ Finset.range trunk, uVar ^ j) * markedSideProduct side +
    sideProduct side *
      (∑ extension ∈ Finset.range trunk,
        uVar ^ (trunk - extension) *
          extendedSideDegree opposite.sum opposite.card extension)

def legIntervalTerm
    (length centerDegree : ℕ) (fullDegree : BivariatePoly)
    (pfx suffix : ℕ) : BivariatePoly :=
  let size := length - pfx - suffix
  let main :=
    if pfx = 0 then
      fullDegree - zVar - bivariateConst (length - 1) * zVar ^ 2 -
        zVar ^ centerDegree + zVar ^ (centerDegree - 1)
    else
      fullDegree - bivariateConst (length - pfx) * zVar ^ 2
  if suffix = 0 then
    uVar ^ size * main
  else
    uVar ^ size * zVar * (main + pathDegree suffix)

def legIntervalFormula
    (length centerDegree : ℕ) (fullDegree : BivariatePoly) : BivariatePoly :=
  ∑ pfx ∈ Finset.range length,
    ∑ suffix ∈ Finset.range (length - pfx),
      legIntervalTerm length centerDegree fullDegree pfx suffix

def trunkIntervalFormula (T : DoubleSpider) : BivariatePoly :=
  ∑ leftExtension ∈ Finset.range (T.trunk - 1),
    ∑ rightExtension ∈ Finset.range (T.trunk - 1 - leftExtension),
      uVar ^ (T.trunk - 1 - leftExtension - rightExtension) * zVar *
        (extendedSideDegree T.left.sum T.left.card leftExtension +
          extendedSideDegree T.right.sum T.right.card rightExtension)

/-- The exact CSF-determined one-hole transform used by the first deck layer.
Its five terms are the both-center, two oriented one-center, pendant-leg,
and trunk-interval sectors. -/
def firstDeckLayer (T : DoubleSpider) : BivariatePoly :=
  let fullDegree := degreePolynomial T
  let bothCenters :=
    uVar ^ (T.trunk + 1) *
      markedSideProduct (T.left + T.right)
  let oneCenter :=
    oneCenterFormula T.left T.trunk T.right +
      oneCenterFormula T.right T.trunk T.left
  let leftLegIntervals :=
    (T.left.map (fun length =>
      legIntervalFormula length (T.left.card + 1) fullDegree)).sum
  let rightLegIntervals :=
    (T.right.map (fun length =>
      legIntervalFormula length (T.right.card + 1) fullDegree)).sum
  bothCenters + oneCenter + leftLegIntervals + rightLegIntervals +
    trunkIntervalFormula T

/-- The four reconstruction clauses are stated at the exact data surface
supplied by the corresponding boundary identity or exceptional grouping
functional. -/
def equalTotalCaseReconstruction_claim29381 : Prop :=
  (∀ T : DoubleSpider, equalTotalDoubleSpider T →
    caseLongTrunk T ∨ caseAdjacentAtLeastThree T ∨
      caseAdjacentTwoByTwo T ∨ caseAdjacentTwoByR T) ∧
  (∀ T T' : DoubleSpider,
    equalTotalDoubleSpider T → equalTotalDoubleSpider T' →
      caseLongTrunk T → caseLongTrunk T' →
      sideBoundaryData T = sideBoundaryData T' →
      sideExchangeEquivalent T T') ∧
  (∀ T T' : DoubleSpider,
    equalTotalDoubleSpider T → equalTotalDoubleSpider T' →
      caseAdjacentAtLeastThree T → caseAdjacentAtLeastThree T' →
      sideBoundaryData T = sideBoundaryData T' →
      sideExchangeEquivalent T T') ∧
  (∀ T T' : DoubleSpider,
    equalTotalDoubleSpider T → equalTotalDoubleSpider T' →
      caseAdjacentTwoByTwo T → caseAdjacentTwoByTwo T' →
      firstDeckLayer T = firstDeckLayer T' →
      sideExchangeEquivalent T T') ∧
  (∀ T T' : DoubleSpider,
    equalTotalDoubleSpider T → equalTotalDoubleSpider T' →
      caseAdjacentTwoByR T → caseAdjacentTwoByR T' →
      exceptionalData T = exceptionalData T' →
      sideExchangeEquivalent T T')

end
end MathlibPlus.Open.ResearchFormalization.BatchR0532
