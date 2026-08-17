import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0524TreeTransforms

open scoped BigOperators

noncomputable section

private def connectedWithin {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (S : Finset V) : Prop :=
  S.Nonempty ∧
    ∀ ⦃x : V⦄, x ∈ S → ∀ ⦃y : V⦄, y ∈ S →
      Relation.ReflTransGen
        (fun a b : V => T.Adj a b ∧ a ∈ S ∧ b ∈ S) x y

private def sameComplementComponent {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (S : Finset V) (x y : V) : Prop :=
  Relation.ReflTransGen
    (fun a b : V => T.Adj a b ∧ a ∉ S ∧ b ∉ S) x y

private def isComponentRepresentative {V : Type*} [Fintype V]
    [DecidableEq V] [LinearOrder V]
    (T : SimpleGraph V) (S : Finset V) (x : V) : Prop :=
  x ∉ S ∧
    ∀ y : V, y ∉ S → sameComplementComponent T S x y → x ≤ y

private noncomputable def complementComponentCount {V : Type*} [Fintype V]
    [DecidableEq V] [LinearOrder V]
    (T : SimpleGraph V) (S : Finset V) : ℕ := by
  classical
  exact (Finset.univ.filter (isComponentRepresentative T S)).card

private def complementFinset {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) : Finset V :=
  Finset.univ.filter (fun x => x ∉ S)

private def graphDegree {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (v : V) : ℕ :=
  Set.ncard (T.neighborSet v)

private noncomputable def boundaryEdgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (S : Finset V) : ℕ := by
  classical
  exact ∑ v ∈ S,
    (Finset.univ.filter (fun w => w ∉ S ∧ T.Adj v w)).card

private noncomputable def connectedSets {V : Type*} [Fintype V]
    [DecidableEq V]
    (T : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact Finset.univ.powerset.filter (fun S => connectedWithin T S)

private noncomputable def treeBoundaryPolynomial {V : Type*} [Fintype V]
    [DecidableEq V] [LinearOrder V]
    (T : SimpleGraph V) : Polynomial (Polynomial ℚ) := by
  classical
  exact ∑ S ∈ connectedSets T,
    Polynomial.monomial S.card
      (Polynomial.monomial (boundaryEdgeCount T S) (1 : ℚ))

private noncomputable def oneHoleSummand {V : Type*} [Fintype V]
    [DecidableEq V] [LinearOrder V]
    (T : SimpleGraph V) (S : Finset V) : Polynomial ℚ := by
  classical
  exact ∑ x ∈ complementFinset S,
    Polynomial.monomial
      (complementComponentCount T (insert x S)) (1 : ℚ)

private noncomputable def oneHolePolynomial {V : Type*} [Fintype V]
    [DecidableEq V] [LinearOrder V]
    (T : SimpleGraph V) : Polynomial (Polynomial ℚ) := by
  classical
  exact ∑ S ∈ connectedSets T,
    Polynomial.monomial S.card (oneHoleSummand T S)

private noncomputable def connectedSizePolynomial {V : Type*} [Fintype V]
    [DecidableEq V] [LinearOrder V]
    (T : SimpleGraph V) : Polynomial ℚ := by
  classical
  exact ∑ S ∈ connectedSets T,
    Polynomial.monomial S.card (1 : ℚ)

private noncomputable def oneHoleAtOnePolynomial {V : Type*} [Fintype V]
    [DecidableEq V] [LinearOrder V]
    (T : SimpleGraph V) : Polynomial ℚ := by
  classical
  exact ∑ S ∈ connectedSets T,
    Polynomial.monomial S.card
      (Polynomial.eval 1 (oneHoleSummand T S))

private noncomputable def boundaryAtOnePolynomial {V : Type*} [Fintype V]
    [DecidableEq V] [LinearOrder V]
    (T : SimpleGraph V) : Polynomial ℚ := by
  classical
  exact ∑ S ∈ connectedSets T,
    Polynomial.monomial S.card (boundaryEdgeCount T S : ℚ)

private noncomputable def oneHoleDerivativeAtOnePolynomial
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (T : SimpleGraph V) : Polynomial ℚ := by
  classical
  exact ∑ S ∈ connectedSets T,
    Polynomial.monomial S.card
      (Polynomial.eval 1 ((oneHoleSummand T S).derivative))

private noncomputable def leafCount {V : Type*} [Fintype V]
    [DecidableEq V]
    (T : SimpleGraph V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun v => graphDegree T v = 1)).card

private noncomputable def leafDegreeTwoEdgeCount {V : Type*} [Fintype V]
    [DecidableEq V]
    (T : SimpleGraph V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun v => graphDegree T v = 1)).sum
    (fun v =>
      (Finset.univ.filter
        (fun w => T.Adj v w ∧ graphDegree T w = 2)).card)

private noncomputable def qPolynomial {V : Type*} [Fintype V]
    [DecidableEq V]
    (T : SimpleGraph V) : Polynomial ℚ := by
  classical
  exact ∑ x ∈ Finset.univ,
    ∑ y ∈ Finset.univ.filter (fun y => y ≠ x),
      Polynomial.monomial
        (graphDegree T x + graphDegree T y - 1) (1 : ℚ)

private noncomputable def edgeDegreePolynomial {V : Type*} [Fintype V]
    [DecidableEq V] [LinearOrder V]
    (T : SimpleGraph V) : Polynomial ℚ := by
  classical
  exact ∑ x ∈ Finset.univ,
    ∑ y ∈ Finset.univ.filter (fun y => x < y ∧ T.Adj x y),
      Polynomial.monomial
        (graphDegree T x + graphDegree T y - 2) (1 : ℚ)

private noncomputable def singletonOneHolePolynomial
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (T : SimpleGraph V) : Polynomial ℚ := by
  classical
  exact ∑ v ∈ Finset.univ, oneHoleSummand T {v}

private def twoVertexDeletionClass {V : Type*} [Fintype V]
    [DecidableEq V]
    (T : SimpleGraph V) (a b : V) : Prop :=
  (graphDegree T a = 1 ∧ graphDegree T b = 1) ∨
    (T.Adj a b ∧
      ((graphDegree T a = 1 ∧ graphDegree T b = 2) ∨
        (graphDegree T a = 2 ∧ graphDegree T b = 1)))

private def deleteTwoVertices {V : Type*} [Fintype V] [DecidableEq V]
    (a b : V) : Finset V :=
  (Finset.univ.erase a).erase b

/-- Claim 22348: the coefficient formula for the boundary totals uses the
boundary-edge derivative of `C_T` and the z-derivative of the deletion-
complement one-hole transform, with the complement-order-two exception and
endpoint retained. -/
def boundaryTotalsAwayFromComplementOrderTwo_claim22348 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (T : SimpleGraph V),
    T.IsTree →
    (∀ m : ℕ, m < Fintype.card V →
      Fintype.card V - m ≠ 2 →
      (boundaryAtOnePolynomial T).coeff m =
        ((oneHoleDerivativeAtOnePolynomial T).coeff m -
          ((Fintype.card V - m : ℕ) : ℚ) *
            (connectedSizePolynomial T).coeff m) /
          (((Fintype.card V - m : ℕ) : ℚ) - 2)) ∧
    (boundaryAtOnePolynomial T).coeff (Fintype.card V) = 0

/-- Claim 22349: two-vertex deletion connectivity has exactly the stated
leaf/leaf and adjacent leaf--degree-two cases, and the resulting C and B
coefficients use the boundary-edge weight. -/
def connectedComplementOrderTwo_claim22349 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (T : SimpleGraph V),
    T.IsTree →
    (∀ a b : V, a ≠ b →
      (connectedWithin T (deleteTwoVertices a b) ↔
        twoVertexDeletionClass T a b) ∧
      ((graphDegree T a = 1 ∧ graphDegree T b = 1 →
          boundaryEdgeCount T (deleteTwoVertices a b) = 2) ∧
        (T.Adj a b ∧
            ((graphDegree T a = 1 ∧ graphDegree T b = 2) ∨
              (graphDegree T a = 2 ∧ graphDegree T b = 1)) →
          boundaryEdgeCount T (deleteTwoVertices a b) = 1))) ∧
    (connectedSizePolynomial T).coeff (Fintype.card V - 2) =
        ((Nat.choose (leafCount T) 2 : ℕ) : ℚ) +
          (leafDegreeTwoEdgeCount T : ℚ) ∧
    (boundaryAtOnePolynomial T).coeff (Fintype.card V - 2) =
        2 * ((Nat.choose (leafCount T) 2 : ℕ) : ℚ) +
          (leafDegreeTwoEdgeCount T : ℚ)

/-- Claim 22350: the singleton coefficient of the exact one-hole transform
recovers the leaf--degree-two edge contribution from the degree-sequence
polynomial. -/
def singletonSectorRecoversLeafDegreeTwoEdges_claim22350 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (T : SimpleGraph V),
    T.IsTree →
    (oneHolePolynomial T).coeff 1 = singletonOneHolePolynomial T ∧
    qPolynomial T - (oneHolePolynomial T).coeff 1 =
      2 * (Polynomial.X - Polynomial.C 1) * edgeDegreePolynomial T ∧
    (edgeDegreePolynomial T).coeff 1 = (leafDegreeTwoEdgeCount T : ℚ)

end

end MathlibPlus.Open.ResearchFormalization.R0524TreeTransforms
