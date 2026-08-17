import MathlibPlus.Open.RootedTreeBoundary
import MathlibPlus.Open.ResearchFormalizationBatch.UPolynomial

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0765Claim26913

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

open MathlibPlus.Open.RootedTreeBoundary

abbrev Coeff26913 := MvPolynomial ℕ ℚ
abbrev RootedFactor26913 := Polynomial Coeff26913
abbrev RootedTree26913 := RootedFiniteTree

private noncomputable def componentMonomial26913
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset (↥G.edgeSet)) : Coeff26913 :=
  let H := MathlibPlus.Open.ResearchFormalizationBatch.selectedSpanningGraph G A
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  ∏ C : H.ConnectedComponent,
    MvPolynomial.X
      (MathlibPlus.Open.ResearchFormalizationBatch.selectedComponentSize G A C)

private noncomputable def unrootedU26913
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Coeff26913 :=
  letI : Fintype (↥G.edgeSet) := Fintype.ofFinite _
  ∑ A ∈ (Finset.univ : Finset (↥G.edgeSet)).powerset,
    componentMonomial26913 G A

private def deletedGraph26913 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) : SimpleGraph {v : V // v ≠ r} :=
  G.induce {v | v ≠ r}

private noncomputable def rootDeletedMonomial26913
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset (↥G.edgeSet)) (r : V) : Coeff26913 :=
  let H := MathlibPlus.Open.ResearchFormalizationBatch.selectedSpanningGraph G A
  let root := H.connectedComponentMk r
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  ∏ C : H.ConnectedComponent,
    if C = root then 1 else MvPolynomial.X
      (MathlibPlus.Open.ResearchFormalizationBatch.selectedComponentSize G A C)

private noncomputable def rootComponentOrder26913
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset (↥G.edgeSet)) (r : V) : ℕ :=
  MathlibPlus.Open.ResearchFormalizationBatch.selectedComponentSize G A
    ((MathlibPlus.Open.ResearchFormalizationBatch.selectedSpanningGraph G A).connectedComponentMk r)

private noncomputable def rootedFactor26913
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) : RootedFactor26913 :=
  letI : Fintype (↥G.edgeSet) := Fintype.ofFinite _
  ∑ A ∈ (Finset.univ : Finset (↥G.edgeSet)).powerset,
    (Polynomial.C (componentMonomial26913 G A) +
      Polynomial.X ^ rootComponentOrder26913 G A r *
        Polynomial.C (rootDeletedMonomial26913 G A r))

private noncomputable def firstCollar26913
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) : RootedFactor26913 :=
  letI : Fintype (↥G.edgeSet) := Fintype.ofFinite _
  ∑ A ∈ (Finset.univ : Finset (↥G.edgeSet)).powerset,
    Polynomial.X ^ (rootComponentOrder26913 G A r - 1) *
      Polynomial.C (rootDeletedMonomial26913 G A r)

private noncomputable def closureOfTree26913 (T : RootedTree26913) : Coeff26913 :=
  letI := T.fintypeV
  letI := T.decidableEqV
  unrootedU26913 T.G

private noncomputable def cavityOfTree26913 (T : RootedTree26913) : Coeff26913 :=
  letI := T.fintypeV
  letI := T.decidableEqV
  unrootedU26913 (deletedGraph26913 T.G T.root)

private noncomputable def rootedFactorOfTree26913
    (T : RootedTree26913) : RootedFactor26913 :=
  letI := T.fintypeV
  letI := T.decidableEqV
  rootedFactor26913 T.G T.root

private noncomputable def firstCollarOfTree26913
    (T : RootedTree26913) : RootedFactor26913 :=
  letI := T.fintypeV
  letI := T.decidableEqV
  firstCollar26913 T.G T.root

private noncomputable def branchClosure26913
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (C : H.ConnectedComponent) : Coeff26913 :=
  letI : Fintype (↥C.supp) := Fintype.ofFinite _
  unrootedU26913 (H.induce C.supp)

private noncomputable def branchClosureProduct26913
    (T : RootedTree26913) : Coeff26913 :=
  letI := T.fintypeV
  letI := T.decidableEqV
  let H := deletedGraph26913 T.G T.root
  ∏ C : H.ConnectedComponent,
    branchClosure26913 H C

/-- Claim 26913: for the exact rooted finite-tree carrier, the open-root
factor has closure U_T at z=0, and the first collar has constant term equal
to the product of the disjoint branch closures, which is the root-deleted
forest polynomial U_(T-r). -/
def claim26913 : Prop :=
  ∀ T : RootedTree26913,
    rootedFactorOfTree26913 T =
        Polynomial.C (closureOfTree26913 T) +
          Polynomial.X * firstCollarOfTree26913 T ∧
      Polynomial.eval 0 (rootedFactorOfTree26913 T) =
        closureOfTree26913 T ∧
        Polynomial.eval 0 (firstCollarOfTree26913 T) =
          branchClosureProduct26913 T ∧
          branchClosureProduct26913 T = cavityOfTree26913 T

end

end MathlibPlus.Open.ResearchFormalization.R0765Claim26913
