import MathlibPlus.Open.RootedTreeBoundary

namespace MathlibPlus.Open.ResearchFormalization.Claim31331

noncomputable section

abbrev ShiftedBoundaryPolynomial := Polynomial (Polynomial ℚ)

def rootZVariable : ShiftedBoundaryPolynomial := Polynomial.X

def rootVVariable : ShiftedBoundaryPolynomial :=
  Polynomial.C (Polynomial.X : Polynomial ℚ)

/-- The source boundary atom `B_R = v + z A_R`. -/
noncomputable def boundaryB (R : RootedTreeBoundary.RootedFiniteTree) :
    ShiftedBoundaryPolynomial :=
  R.normalizedBoundaryFactor ℚ

/-- The shifted atom `D_R = B_R - v(1-v-z) = v² + z(A_R+v)`. -/
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

/-- A leaf child is a degree-one neighbor of the distinguished root. -/
def hasRootLeafChild (R : RootedTreeBoundary.RootedFiniteTree) : Prop :=
  ∃ leaf : R.V,
    R.root ≠ leaf ∧ R.G.Adj R.root leaf ∧ rootedTreeDegree R leaf = 1

/-- `S` is the rooted tree obtained from `R` by deleting one specified root
leaf; the graph isomorphism identifies its vertices and root with the induced
complement. -/
def rootLeafDeletion
    (R S : RootedTreeBoundary.RootedFiniteTree) : Prop :=
  ∃ leaf : R.V, ∃ hroot : R.root ≠ leaf,
    R.G.Adj R.root leaf ∧ rootedTreeDegree R leaf = 1 ∧
      ∃ e : R.G.induce {x : R.V | x ≠ leaf} ≃g S.G,
        e ⟨R.root, hroot⟩ = S.root

/--
For every rooted finite tree, the shifted boundary polynomial is reducible
exactly at a root leaf.  Every supplied one-leaf deletion receives the stated
factorization, and the order-two value is retained.
-/
def completeReducibilityCriterion_claim31331 : Prop :=
  ∀ R : RootedTreeBoundary.RootedFiniteTree,
    ((¬ Irreducible (shiftedBoundaryD R)) ↔ hasRootLeafChild R) ∧
      (∀ S : RootedTreeBoundary.RootedFiniteTree,
        rootLeafDeletion R S →
          shiftedBoundaryD R =
            (rootVVariable + rootZVariable) * boundaryB S) ∧
      (vertexCount R = 2 →
        shiftedBoundaryD R = (rootVVariable + rootZVariable) ^ 2)

end

end MathlibPlus.Open.ResearchFormalization.Claim31331
