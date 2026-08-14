import Mathlib

namespace MathlibPlus.Open.RootedTreeBoundary

open scoped BigOperators

/-- A finite tree together with a distinguished root. -/
structure RootedFiniteTree where
  V : Type
  fintypeV : Fintype V
  decidableEqV : DecidableEq V
  G : SimpleGraph V
  root : V
  isTree : G.IsTree

namespace RootedFiniteTree

private noncomputable instance instFintype (R : RootedFiniteTree) : Fintype R.V := R.fintypeV
private noncomputable instance instDecidableEq (R : RootedFiniteTree) : DecidableEq R.V := R.decidableEqV

/-- The number of edges induced by a finite vertex set. -/
noncomputable def inducedEdgeCount (R : RootedFiniteTree) (S : Finset R.V) : ℕ := by
  classical
  exact (∑ x ∈ S, (S.filter (R.G.Adj x)).card) / 2

/-- The number of tree edges leaving a finite vertex set. -/
noncomputable def boundarySize (R : RootedFiniteTree) (S : Finset R.V) : ℕ := by
  classical
  exact ∑ x ∈ S, ((Finset.univ \ S).filter (R.G.Adj x)).card

/-- A vertex set is one of the connected rooted subtrees used by the boundary polynomial. -/
def isRootedConnected (R : RootedFiniteTree) (S : Finset R.V) : Prop :=
  R.root ∈ S ∧ (R.G.induce (↑S : Set R.V)).Connected

/-- The connected rooted subtree boundary polynomial, with outer variable `u`
(the induced-edge count) and coefficient variable `v` (the boundary size). -/
noncomputable def connectedRootedSubtreeBoundaryPolynomial
    (R : RootedFiniteTree) (K : Type*) [CommRing K] : Polynomial (Polynomial K) := by
  classical
  exact ∑ S ∈ Finset.univ.powerset,
    if R.isRootedConnected S then
      (Polynomial.X : Polynomial (Polynomial K)) ^ R.inducedEdgeCount S *
        Polynomial.C ((Polynomial.X : Polynomial K) ^ R.boundarySize S)
    else 0

/-- `B_R = v + u A_R`, represented as a polynomial in `u` over `K[v]`. -/
noncomputable def normalizedBoundaryFactor
    (R : RootedFiniteTree) (K : Type*) [CommRing K] : Polynomial (Polynomial K) := by
  exact Polynomial.C (Polynomial.X : Polynomial K) +
    Polynomial.X * R.connectedRootedSubtreeBoundaryPolynomial K

/-- Root-preserving graph isomorphism of finite rooted trees. -/
def RootedIso (R S : RootedFiniteTree) : Prop :=
  ∃ f : R.G ≃g S.G, f R.root = S.root

end RootedFiniteTree

/-- Claim 27002: the normalized factor has the stated Eisenstein data and is
irreducible over `ℚ[v]`. -/
def normalized_boundary_factors_are_eisenstein : Prop :=
  ∀ (R : RootedFiniteTree),
    let B := R.normalizedBoundaryFactor ℚ
    B.Monic ∧
      B.natDegree = Fintype.card R.V ∧
      (∀ j < B.natDegree, Polynomial.X ∣ B.coeff j) ∧
      B.coeff 0 = Polynomial.X ∧
      ¬(Polynomial.X ^ 2 ∣ B.coeff 0) ∧
      Irreducible B

/-- Claim 27003: equality of boundary polynomials is equivalent to rooted-tree
isomorphism. -/
def boundary_polynomial_rigidly_determines_rooted_tree : Prop :=
  ∀ (R S : RootedFiniteTree),
    R.connectedRootedSubtreeBoundaryPolynomial ℚ =
        S.connectedRootedSubtreeBoundaryPolynomial ℚ ↔
      RootedFiniteTree.RootedIso R S

/-- Claim 27013: the factor and reconstruction statements persist in every
prime characteristic. -/
def boundary_factors_rigid_in_prime_characteristic : Prop :=
  ∀ (p : ℕ), Nat.Prime p →
    ∀ (R : RootedFiniteTree),
      let B := R.normalizedBoundaryFactor (ZMod p)
      (B.Monic ∧
        (∀ j < B.natDegree, Polynomial.X ∣ B.coeff j) ∧
        B.coeff 0 = Polynomial.X ∧
        ¬(Polynomial.X ^ 2 ∣ B.coeff 0)) ∧
      ∀ A C : RootedFiniteTree,
        A.normalizedBoundaryFactor (ZMod p) =
            C.normalizedBoundaryFactor (ZMod p) ↔
          RootedFiniteTree.RootedIso A C

end MathlibPlus.Open.RootedTreeBoundary
