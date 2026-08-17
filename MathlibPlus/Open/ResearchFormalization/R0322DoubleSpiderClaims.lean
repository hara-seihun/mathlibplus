import MathlibPlus.Open.Research.FormalizationBatchUPolynomial

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization.R0322DoubleSpiderClaims

noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

abbrev ScalarPoly := MvPolynomial (Fin 3) (Polynomial ℚ)

def yVar : ScalarPoly := MvPolynomial.X 0
def xVar : ScalarPoly := MvPolynomial.X 1
def qVar : ScalarPoly := MvPolynomial.X 2

def tMonomial (k : ℕ) : ScalarPoly :=
  MvPolynomial.C (Polynomial.X ^ k)

def scalarConst (r : ℚ) : ScalarPoly :=
  MvPolynomial.C (Polynomial.C r)

def tVar : ScalarPoly := tMonomial 1

def weightedComponentProduct {V : Type} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) : ScalarPoly :=
  ∏ C ∈ MathlibPlus.Open.ResearchFormalizationBatch.uComponents E,
    if C.card = 1 then yVar else 1 + xVar * qVar ^ (C.card - 1)

/-- The singleton-refined signed cut polynomial with independent variables
`Y`, `X`, and `Q`, and outer polynomial variable `t`. -/
def cutPolynomial {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ScalarPoly :=
  ∑ E ∈
      (MathlibPlus.Open.ResearchFormalizationBatch.uEdgeUniverse G).powerset,
    scalarConst ((-1 : ℚ) ^
        ((MathlibPlus.Open.ResearchFormalizationBatch.uEdgeUniverse G).card -
          E.card)) *
      tMonomial E.card * weightedComponentProduct E

def specializeY (P : ScalarPoly) : ScalarPoly :=
  MvPolynomial.eval₂
    (MvPolynomial.C : Polynomial ℚ →+* ScalarPoly)
    (fun i => if i = (0 : Fin 3) then 1 + xVar else MvPolynomial.X i) P

def deckSeries {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ScalarPoly :=
  specializeY ((MvPolynomial.pderiv 0) (cutPolynomial G))

def deckCoefficient {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (s : ℕ) : Polynomial ℚ :=
  (deckSeries G).coeff
    (Finsupp.single (1 : Fin 3) 1 + Finsupp.single (2 : Fin 3) (s - 1))

def boundaryEdgeSet {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : Finset (Sym2 V) :=
  (MathlibPlus.Open.ResearchFormalizationBatch.uEdgeUniverse G).filter
    (fun e => ∃ u v, e = s(u, v) ∧
      ((u ∈ S ∧ v ∉ S) ∨ (u ∉ S ∧ v ∈ S)) ∧ G.Adj u v)

def incidentEdgeSet {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) : Finset (Sym2 V) :=
  (MathlibPlus.Open.ResearchFormalizationBatch.uEdgeUniverse G).filter
    (fun e => ∃ w, e = s(v, w) ∧ G.Adj v w)

def connectedPair {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (s h : ℕ) (v : V) (S : Finset V) : Prop :=
  v ∉ S ∧ S.Nonempty ∧ S.card = s ∧
    (G.induce (S : Set V)).Connected ∧
    (boundaryEdgeSet G S ∪ incidentEdgeSet G v).card = h

def connectedPairCount {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (s h : ℕ) : ℕ :=
  Nat.card {p : V × Finset V // connectedPair G s h p.1 p.2}

def bernsteinCoefficientSumExact {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (s : ℕ) : Polynomial ℚ :=
  let n := Fintype.card V
  ((-1 : ℚ) ^ (s - 1)) •
    ∑ h ∈ Finset.range (n - s + 1),
      (connectedPairCount G s h : Polynomial ℚ) *
        Polynomial.X ^ h * (Polynomial.X - 1) ^ (n - s - h)

def bernsteinExtractionInjective {V : Type} [Fintype V] [DecidableEq V]
    (T U : SimpleGraph V) : Prop :=
  (∀ s : ℕ, deckCoefficient T s = deckCoefficient U s) →
    ∀ s h : ℕ, connectedPairCount T s h = connectedPairCount U s h

/-- A finite ordered occurrence family represents a repeated leg-length
multiset without discarding equal legs. -/
structure LegFamily where
  count : ℕ
  length : Fin count → ℕ

def positiveLegFamily (A : LegFamily) : Prop :=
  ∀ i, 0 < A.length i

def legSum (A : LegFamily) : ℕ :=
  ∑ i : Fin A.count, A.length i

def legMultiset (A : LegFamily) : Multiset ℕ :=
  (Finset.univ : Finset (Fin A.count)).val.map A.length

abbrev LegVertex (A : LegFamily) :=
  Σ i : Fin A.count, Fin (A.length i)

abbrev DoubleSpiderVertex (A B : LegFamily) (c : ℕ) :=
  Fin (c + 1) ⊕ (LegVertex A ⊕ LegVertex B)

def legAdjacent {A : LegFamily} (x y : LegVertex A) : Prop :=
  x.1 = y.1 ∧
    (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)

def doubleSpiderRelation (A B : LegFamily) (c : ℕ)
    (u v : DoubleSpiderVertex A B c) : Prop :=
  match u, v with
  | Sum.inl r, Sum.inl s => r.val + 1 = s.val
  | Sum.inl r, Sum.inr (Sum.inl x) => r.val = 0 ∧ x.2.val = 0
  | Sum.inr (Sum.inl x), Sum.inl r => r.val = 0 ∧ x.2.val = 0
  | Sum.inl r, Sum.inr (Sum.inr x) => r.val = c ∧ x.2.val = 0
  | Sum.inr (Sum.inr x), Sum.inl r => r.val = c ∧ x.2.val = 0
  | Sum.inr (Sum.inl x), Sum.inr (Sum.inl y) => legAdjacent x y
  | Sum.inr (Sum.inr x), Sum.inr (Sum.inr y) => legAdjacent x y
  | _, _ => False

def doubleSpiderGraph (A B : LegFamily) (c : ℕ) :
    SimpleGraph (DoubleSpiderVertex A B c) :=
  SimpleGraph.fromRel (doubleSpiderRelation A B c)

def admissibleDoubleSpider (A B : LegFamily) (c : ℕ) : Prop :=
  1 ≤ c ∧ 2 ≤ A.count ∧ 2 ≤ B.count ∧
    positiveLegFamily A ∧ positiveLegFamily B

def sideExchangeEquivalent
    (A B A' B' : LegFamily) (c c' : ℕ) : Prop :=
  c = c' ∧
    ((legMultiset A = legMultiset A' ∧ legMultiset B = legMultiset B') ∨
      (legMultiset A = legMultiset B' ∧ legMultiset B = legMultiset A'))

def doubleSpiderCutPolynomial
    (A B : LegFamily) (c : ℕ) : ScalarPoly :=
  cutPolynomial (doubleSpiderGraph A B c)

def endpointResponse (a : ℕ) : Fin 3 → ScalarPoly :=
  Matrix.mulVec
    (!![tVar * yVar, -1, -xVar * qVar;
        tVar, -1, 0;
        tVar, 0, -qVar] ^ (a - 1)) ![yVar, 1, 1]

def alphaFactor (a : ℕ) : ScalarPoly :=
  tMonomial 1 * endpointResponse a 0 - endpointResponse a 1

def betaFactor (a : ℕ) : ScalarPoly :=
  tMonomial 1 * endpointResponse a 0 - qVar * endpointResponse a 2

def sideUResponse (A : LegFamily) : ScalarPoly :=
  ∏ i : Fin A.count, alphaFactor (A.length i)

def sideSResponse (A : LegFamily) : ScalarPoly :=
  ∏ i : Fin A.count, betaFactor (A.length i)

def sideZResponse (A : LegFamily) : ScalarPoly :=
  ∏ i : Fin A.count, tMonomial 1 * endpointResponse (A.length i) 0

def sideResponse (A : LegFamily) : Fin 3 → ScalarPoly :=
  ![sideUResponse A + xVar * sideSResponse A +
      (yVar - 1 - xVar) * sideZResponse A,
    sideUResponse A, sideSResponse A]

def bridgeMatrix : Matrix (Fin 3) (Fin 3) ScalarPoly :=
  !![tMonomial 1, 0, 0;
     0, -1, 0;
     0, 0, -xVar * qVar]

def transferMatrix : Matrix (Fin 3) (Fin 3) ScalarPoly :=
  !![tMonomial 1 * yVar, -1, -xVar * qVar;
     tMonomial 1, -1, 0;
     tMonomial 1, 0, -qVar]

def bilinearResponse (u v : Fin 3 → ScalarPoly)
    (K : Matrix (Fin 3) (Fin 3) ScalarPoly) : ScalarPoly :=
  ∑ i : Fin 3, ∑ j : Fin 3, u i * K i j * v j

/-- Claim 19826: the exact ordered connected-pair counts occur in the
Bernstein coefficient of the normalized deck series, and the triangular
orders at `t=0` make that coefficient map injective. -/
def connectedSetBernsteinExtraction_claim19826 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V), T.IsTree →
    ∀ s : ℕ, 1 ≤ s → s ≤ Fintype.card V →
      deckCoefficient T s = bernsteinCoefficientSumExact T s ∧
        (∀ U : SimpleGraph V, U.IsTree →
          (∀ r : ℕ, deckCoefficient T r = deckCoefficient U r) →
            ∀ h : ℕ, connectedPairCount T s h =
              connectedPairCount U s h)

/-- Claim 19830: the singleton-refined cut polynomial of every admissible
labeled double spider has the exact three-state bridge factorization, and its
normalized deck series is the corresponding `Y` derivative at `Y=1+X`. -/
def allOrderDoubleSpiderTransferFactorization_claim19830 : Prop :=
  ∀ (A B : LegFamily) (c : ℕ),
    admissibleDoubleSpider A B c →
      doubleSpiderCutPolynomial A B c =
        bilinearResponse (sideResponse A) (sideResponse B)
          (bridgeMatrix * transferMatrix ^ (c - 1)) ∧
      deckSeries (doubleSpiderGraph A B c) =
        specializeY
          ((MvPolynomial.pderiv 0)
            (bilinearResponse (sideResponse A) (sideResponse B)
              (bridgeMatrix * transferMatrix ^ (c - 1)))) ∧
      transferMatrix.transpose * bridgeMatrix =
        bridgeMatrix * transferMatrix

abbrev BoundaryPoly := MvPolynomial (Fin 2) ℚ

def uBoundaryVar : BoundaryPoly := MvPolynomial.X 0
def vBoundaryVar : BoundaryPoly := MvPolynomial.X 1

def boundaryPolynomial {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : BoundaryPoly :=
  ∑ S ∈ (Finset.univ : Finset (Finset V)).filter (fun S : Finset V =>
    S.Nonempty ∧ (G.induce (S : Set V)).Connected),
    uBoundaryVar ^ S.card *
      vBoundaryVar ^ (boundaryEdgeSet G S).card

def boundaryPolynomialVOne {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Polynomial ℚ :=
  MvPolynomial.eval₂
    (Polynomial.C : ℚ →+* Polynomial ℚ)
    (fun i => if i = (0 : Fin 2) then Polynomial.X else 1)
    (boundaryPolynomial G)

def degreeSequence {V : Type} [Fintype V] (G : SimpleGraph V) : Multiset ℕ :=
  (Finset.univ : Finset V).val.map (fun v => G.degree v)

/-- Claim 19835: the two displayed nonisomorphic double spiders have equal
size-only boundary specialization and distinct full boundary polynomial. -/
def sizeOnlyBoundarySpecializationInsufficient_claim19835 : Prop :=
  let A₁ : LegFamily := {count := 2, length := ![1, 1]}
  let B₁ : LegFamily := {count := 2, length := ![2, 4]}
  let A₂ : LegFamily := {count := 2, length := ![1, 3]}
  let B₂ : LegFamily := {count := 2, length := ![1, 3]}
  let G₁ := doubleSpiderGraph A₁ B₁ 1
  let G₂ := doubleSpiderGraph A₂ B₂ 1
  degreeSequence G₁ = degreeSequence G₂ ∧
    boundaryPolynomialVOne G₁ = boundaryPolynomialVOne G₂ ∧
    boundaryPolynomial G₁ ≠ boundaryPolynomial G₂ ∧
    ¬ Nonempty (G₁ ≃g G₂)

/-- Claim 19838: on balanced adjacent-center double spiders, equality of the
complete normalized deck layer forces the two side multisets up to exchange. -/
def balancedAdjacentCenterDoubleSpiderDeckReconstruction_claim19838 : Prop :=
  ∀ (A B A' B' : LegFamily) (d N : ℕ),
    admissibleDoubleSpider A B 1 →
    admissibleDoubleSpider A' B' 1 →
    A.count = d → B.count = d → A'.count = d → B'.count = d →
    2 ≤ d → legSum A = N → legSum B = N →
    legSum A' = N → legSum B' = N →
    deckSeries (doubleSpiderGraph A B 1) =
      deckSeries (doubleSpiderGraph A' B' 1) →
    sideExchangeEquivalent A B A' B' 1 1

end

end MathlibPlus.Open.ResearchFormalization.R0322DoubleSpiderClaims
