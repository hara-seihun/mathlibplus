import MathlibPlus.Open.RootedTreeBoundary

namespace MathlibPlus.Open.ResearchFormalization.Claim31332

noncomputable section

abbrev ShiftedBoundaryPolynomial := Polynomial (Polynomial ℚ)

def rootZVariable : ShiftedBoundaryPolynomial := Polynomial.X

def rootVVariable : ShiftedBoundaryPolynomial :=
  Polynomial.C (Polynomial.X : Polynomial ℚ)

noncomputable def boundaryB (R : RootedTreeBoundary.RootedFiniteTree) :
    ShiftedBoundaryPolynomial :=
  R.normalizedBoundaryFactor ℚ

noncomputable def shiftedBoundaryD
    (R : RootedTreeBoundary.RootedFiniteTree) : ShiftedBoundaryPolynomial :=
  boundaryB R - rootVVariable * (1 - rootVVariable - rootZVariable)

noncomputable def rootedTreeDegree
    (R : RootedTreeBoundary.RootedFiniteTree) (x : R.V) : ℕ := by
  classical
  letI : Fintype R.V := R.fintypeV
  letI : DecidableEq R.V := R.decidableEqV
  exact (Finset.univ.filter (R.G.Adj x)).card

def vertexCount (R : RootedTreeBoundary.RootedFiniteTree) : ℕ := by
  letI : Fintype R.V := R.fintypeV
  exact Fintype.card R.V

def hasRootLeafChild (R : RootedTreeBoundary.RootedFiniteTree) : Prop :=
  ∃ leaf : R.V,
    R.root ≠ leaf ∧ R.G.Adj R.root leaf ∧ rootedTreeDegree R leaf = 1

def rootLeafDeletion
    (R S : RootedTreeBoundary.RootedFiniteTree) : Prop :=
  ∃ leaf : R.V, ∃ hroot : R.root ≠ leaf,
    R.G.Adj R.root leaf ∧ rootedTreeDegree R leaf = 1 ∧
      ∃ e : R.G.induce {x : R.V | x ≠ leaf} ≃g S.G,
        e ⟨R.root, hroot⟩ = S.root

/-- The factor and reconstruction data used in the fixed-order product claim. -/
def rootedBoundaryFactorClassification
    (R : RootedTreeBoundary.RootedFiniteTree) : Prop :=
  boundaryB R ≠ 0 ∧
    (boundaryB R).Monic ∧
    Irreducible (boundaryB R) ∧
    (∀ S : RootedTreeBoundary.RootedFiniteTree,
      ¬ RootedTreeBoundary.RootedFiniteTree.RootedIso R S →
        boundaryB R ≠ boundaryB S) ∧
    (∀ S : RootedTreeBoundary.RootedFiniteTree,
      rootLeafDeletion R S →
        shiftedBoundaryD R =
          (rootVVariable + rootZVariable) * boundaryB S) ∧
    (¬ hasRootLeafChild R → Irreducible (shiftedBoundaryD R)) ∧
    (∀ S : RootedTreeBoundary.RootedFiniteTree,
      ¬ RootedTreeBoundary.RootedFiniteTree.RootedIso R S →
        shiftedBoundaryD R ≠ shiftedBoundaryD S) ∧
    Polynomial.coeff (boundaryB R) 0 =
      (Polynomial.X : Polynomial ℚ) ∧
    Polynomial.coeff (shiftedBoundaryD R) 0 =
      (Polynomial.X : Polynomial ℚ) ^ 2

def rootedBoundaryMultisetProduct
    (E : Multiset RootedTreeBoundary.RootedFiniteTree) :
    ShiftedBoundaryPolynomial :=
  (E.map shiftedBoundaryD).prod

/--
For one fixed order at least three, the exact shifted-atom classification
recovers the rooted-tree multiset from equality of products.
-/
def fixedOrderProductRigidity_claim31332 : Prop :=
  ∀ (d : ℕ)
    (E F : Multiset RootedTreeBoundary.RootedFiniteTree),
    3 ≤ d →
    (∀ R ∈ E, vertexCount R = d) →
    (∀ R ∈ F, vertexCount R = d) →
      (∀ R : RootedTreeBoundary.RootedFiniteTree,
        vertexCount R = d → rootedBoundaryFactorClassification R) ∧
      (rootedBoundaryMultisetProduct E = rootedBoundaryMultisetProduct F →
        Multiset.Rel RootedTreeBoundary.RootedFiniteTree.RootedIso E F)

end

end MathlibPlus.Open.ResearchFormalization.Claim31332
