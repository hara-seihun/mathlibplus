import MathlibPlus.Open.RootedTreeBoundary
import MathlibPlus.Open.ResearchFormalizationBatch.UPolynomial

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization.R0765RootedFactorClaims26912_26914

noncomputable section

open MathlibPlus.Open.RootedTreeBoundary
open MathlibPlus.Open.ResearchFormalizationBatch

abbrev Coeff := MvPolynomial ℕ ℚ
abbrev RootedFactor := Polynomial Coeff
abbrev RootedTree := RootedFiniteTree

/-- The unrooted component-profile monomial in the exact coefficient ring. -/
noncomputable def componentMonomialQ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset (↥G.edgeSet)) : Coeff :=
  MvPolynomial.map (Nat.castRingHom ℚ) (spanningComponentMonomial G A)

/-- The component order containing a distinguished root in a selected state. -/
def rootComponentOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset (↥G.edgeSet)) (r : V) : ℕ :=
  selectedComponentSize G A
    ((selectedSpanningGraph G A).connectedComponentMk r)

/-- The selected-state component product with the root component removed. -/
noncomputable def rootDeletedMonomialQ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset (↥G.edgeSet)) (r : V) : Coeff :=
  let H := selectedSpanningGraph G A
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  let rootClass := H.connectedComponentMk r
  ∏ C : H.ConnectedComponent,
    if C = rootClass then 1 else MvPolynomial.X (selectedComponentSize G A C)

/-- The exact rooted factor from the selected-edge component expansion. -/
noncomputable def rootedFactor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) : RootedFactor :=
  letI : Fintype (↥G.edgeSet) := Fintype.ofFinite _
  Finset.sum
    ((Finset.univ : Finset (↥G.edgeSet)).powerset)
    (fun A =>
      Polynomial.C (componentMonomialQ G A) +
        Polynomial.X ^ rootComponentOrder G A r *
          Polynomial.C (rootDeletedMonomialQ G A r))

/-- The exact unrooted closure polynomial. -/
noncomputable def unrootedU
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Coeff :=
  letI : Fintype (↥G.edgeSet) := Fintype.ofFinite _
  Finset.sum
    ((Finset.univ : Finset (↥G.edgeSet)).powerset)
    (fun A => componentMonomialQ G A)

/-- The graph obtained by deleting the distinguished root. -/
def deletedGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) : SimpleGraph {v : V // v ≠ r} :=
  G.induce {v | v ≠ r}

/-- The graph carried by one connected component of the root-deleted graph. -/
def branchGraph (T : RootedTree)
    (C : (deletedGraph T.G T.root).ConnectedComponent) : SimpleGraph
      {v : {v : T.V // v ≠ T.root} //
        (deletedGraph T.G T.root).connectedComponentMk v = C} :=
  (deletedGraph T.G T.root).induce
    {v | (deletedGraph T.G T.root).connectedComponentMk v = C}

/-- A rooted branch is the actual root-deleted connected component, rooted at
its vertex attached to the deleted root. -/
def isRootedBranch (T : RootedTree)
    (C : (deletedGraph T.G T.root).ConnectedComponent)
    (D : RootedTree) : Prop :=
  ∃ e : D.G ≃g branchGraph T C,
    T.G.Adj T.root (e D.root).1.1

/-- Product of the rooted factors of one actual branch family. -/
noncomputable def branchFactorProduct (T : RootedTree)
    (q : (deletedGraph T.G T.root).ConnectedComponent → RootedTree) : RootedFactor :=
  letI : Fintype (deletedGraph T.G T.root).ConnectedComponent := Fintype.ofFinite _
  ∏ C, rootedFactor (q C).G (q C).root

/-- Product of the unrooted closures of one actual branch family. -/
noncomputable def branchClosureProduct (T : RootedTree)
    (q : (deletedGraph T.G T.root).ConnectedComponent → RootedTree) : Coeff :=
  letI : Fintype (deletedGraph T.G T.root).ConnectedComponent := Fintype.ofFinite _
  ∏ C, unrootedU (q C).G

/-- Claim 26912: the rooted factor has the exact open-root decomposition with
one rooted factor for each actual branch of the root-deleted tree. -/
def claim26912 : Prop :=
  ∀ T : RootedTree,
    ∃ q : (deletedGraph T.G T.root).ConnectedComponent → RootedTree,
      (∀ C, isRootedBranch T C (q C)) ∧
        rootedFactor T.G T.root =
          Polynomial.C (unrootedU T.G) +
            Polynomial.X * branchFactorProduct T q

/-- Weighted homogeneity in the actual `x_j` variables. -/
def weightedHomogeneous (m : ℕ) (p : Coeff) : Prop :=
  ∀ e ∈ p.support,
    e.support.sum (fun j a => j * a) = m

/-- Monicity and independence of the top variable `x_m`. -/
def monicLinearInTop (m : ℕ) (p : Coeff) : Prop :=
  ∃ a : Coeff,
    p = MvPolynomial.X m + a ∧
      ∀ e ∈ a.support, e m = 0

/-- The normalized irreducible predicate for the actual unrooted closure. -/
def normalizedIrreducible (m : ℕ) (p : Coeff) : Prop :=
  p ≠ 0 ∧
    weightedHomogeneous m p ∧
      monicLinearInTop m p ∧
        Irreducible p

/-- Claim 26914: every actual rooted finite tree has a weighted-homogeneous,
monic-linear, normalized irreducible unrooted closure polynomial. -/
def claim26914 : Prop :=
  ∀ T : RootedTree,
    normalizedIrreducible (Fintype.card T.V) (unrootedU T.G)

end

end MathlibPlus.Open.ResearchFormalization.R0765RootedFactorClaims26912_26914
