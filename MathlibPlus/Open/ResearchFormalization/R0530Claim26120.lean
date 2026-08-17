import MathlibPlus.Open.ResearchFormalization.BatchR0532Claims29380_29381

namespace MathlibPlus.Open.ResearchFormalization.R0530Claim26120

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization.BatchR0532
open Polynomial

noncomputable section

/-- The path factor `q_a = 1 + x + ... + x^a` in the reversed boundary jet. -/
def boundaryQ (a : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (a + 1), (Polynomial.X : Polynomial ℤ) ^ k

/-- The positive-degree path factor `t_a = x + ... + x^a`. -/
def boundaryT (a : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range a, (Polynomial.X : Polynomial ℤ) ^ (k + 1)

/-- The product `Q_C` over a repeated leg multiset. -/
def boundaryQProduct (C : Multiset ℕ) : Polynomial ℤ :=
  (C.map boundaryQ).prod

/-- The marked product sum `M_C` over a repeated leg multiset. -/
def boundaryMarkedProduct (C : Multiset ℕ) : Polynomial ℤ :=
  (C.map (fun a => boundaryT a * boundaryQProduct (C.erase a))).sum

/-- The internal excess contribution in the reversed boundary jet. -/
def boundaryInternalExcess
    (A B : Multiset ℕ) (c : ℕ) : Polynomial ℤ :=
  let n := A.sum + B.sum + c + 1
  let legPart :=
    ((A + B).map (fun a =>
      ∑ k ∈ Finset.Ico 1 a,
        ((a - k : ℕ) : ℤ) * (Polynomial.X : Polynomial ℤ) ^ (n - k))).sum
  let trunkPart :=
    ∑ k ∈ Finset.Ico 1 c,
      ((c - k : ℕ) : ℤ) * (Polynomial.X : Polynomial ℤ) ^ (n - k)
  legPart + trunkPart

/-- The exact reversed excess-boundary jet from the first-deck layer. -/
def reversedExcessBoundaryJet
    (A B : Multiset ℕ) (c : ℕ) : Polynomial ℤ :=
  (boundaryMarkedProduct (A + B) - boundaryQProduct (A + B)) +
    (∑ k ∈ Finset.range c, (Polynomial.X : Polynomial ℤ) ^ k) *
      ((Polynomial.X : Polynomial ℤ) ^ (B.sum + 1) *
          boundaryMarkedProduct A +
        (Polynomial.X : Polynomial ℤ) ^ (A.sum + 1) *
          boundaryMarkedProduct B) +
    boundaryInternalExcess A B c

/-- The folded monomial `E_j = y^j + y^(n-1-j)` in the marked two-edge layer. -/
def markedEdgeFold (n j : ℕ) : Polynomial ℤ :=
  (Polynomial.X : Polynomial ℤ) ^ j +
    (Polynomial.X : Polynomial ℤ) ^ (n - 1 - j)

/-- One pendant-leg contribution to the marked two-edge polynomial. -/
def markedPendantContribution
    (n legs d : ℕ) : Polynomial ℤ :=
  Polynomial.C ((legs + 1 : ℕ) : ℤ) *
      (∑ j ∈ Finset.Ico 1 d, markedEdgeFold n j) +
    Polynomial.C ((legs - 1 : ℕ) : ℤ) * markedEdgeFold n d

/-- The marked two-edge response after the ordinary degree-two unfolding. -/
def markedTwoEdgePolynomial
    (A B : Multiset ℕ) (c : ℕ) : Polynomial ℤ :=
  let n := A.sum + B.sum + c + 1
  let p := A.card
  let q := B.card
  let legs := p + q
  let r := A.sum + 1
  ((A + B).map (markedPendantContribution n legs)).sum +
    Polynomial.C (p : ℤ) * markedEdgeFold n (r - 1) +
    Polynomial.C ((legs + 1 : ℕ) : ℤ) *
      (∑ j ∈ Finset.Ico r (r + c - 1), markedEdgeFold n j) +
    Polynomial.C (q : ℤ) * markedEdgeFold n (r + c - 1)

/-- The canonical orientation of an unequal double spider.  The side with
    smaller total is selected before the two response surfaces are formed, so
    the predicate and the conclusion are invariant under side exchange. -/
def unequalTwoLegSmallSide
    (T : DoubleSpider) : Prop :=
  admissibleDoubleSpider T ∧
    T.left.sum ≠ T.right.sum ∧
      (if T.left.sum < T.right.sum then T.left else T.right).card = 2

/-- The exact pair of observed surfaces used for the reconstruction: the
    reversed excess-boundary jet and the marked two-edge polynomial. -/
def boundaryAndMarkedSurface
    (T : DoubleSpider) : Polynomial ℤ × Polynomial ℤ :=
  let A := if T.left.sum < T.right.sum then T.left else T.right
  let B := if T.left.sum < T.right.sum then T.right else T.left
  (reversedExcessBoundaryJet A B T.trunk,
    markedTwoEdgePolynomial A B T.trunk)

/-- Claim 26120: for an unequal-total double spider whose smaller side has two
    legs, equality of the recovered boundary surface and the marked two-edge
    unfolding recovers the trunk and the complete global leg multiset. -/
def claim26120_reconstructsTrunkAndGlobalLegs : Prop :=
  ∀ T T' : DoubleSpider,
    unequalTwoLegSmallSide T →
      unequalTwoLegSmallSide T' →
        boundaryAndMarkedSurface T = boundaryAndMarkedSurface T' →
          T.trunk = T'.trunk ∧
            globalLegMultiset T = globalLegMultiset T'

end

end MathlibPlus.Open.ResearchFormalization.R0530Claim26120
