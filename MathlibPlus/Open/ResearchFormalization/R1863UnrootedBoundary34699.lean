import MathlibPlus.Open.RootedTreeBoundary

namespace MathlibPlus.Open.ResearchFormalization.R1863UnrootedBoundary34699

open MathlibPlus.Open.RootedTreeBoundary
open Classical
attribute [local instance] Classical.propDecidable

noncomputable section

/-- The connected-subtree boundary polynomial without the rooted condition,
using the same finite graph, induced-edge, and boundary-edge carriers as the
reviewed rooted boundary polynomial. -/
noncomputable def connectedSubtreeBoundaryPolynomial
    (R : RootedFiniteTree) (K : Type*) [CommRing K] : Polynomial (Polynomial K) :=
  letI := R.fintypeV
  letI := R.decidableEqV
  ∑ S ∈ Finset.univ.powerset,
    if (R.G.induce (↑S : Set R.V)).Connected then
      (Polynomial.X : Polynomial (Polynomial K)) ^
          R.inducedEdgeCount S *
        Polynomial.C ((Polynomial.X : Polynomial K) ^ R.boundarySize S)
    else 0

end

end MathlibPlus.Open.ResearchFormalization.R1863UnrootedBoundary34699
