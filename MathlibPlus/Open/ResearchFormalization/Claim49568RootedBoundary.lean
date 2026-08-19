import MathlibPlus.Open.RootedBoundaryLayers

namespace MathlibPlus.Open.ResearchFormalization.Claim49568

abbrev RTree := MathlibPlus.Open.RootedBoundaryLayers.RootedTree
abbrev BPoly := MathlibPlus.Open.RootedBoundaryLayers.BoundaryPolynomial

/-- The actual child-boundary product of a finite rooted tree. -/
noncomputable def childBoundaryProduct (R : RTree) : BPoly :=
  match R with
  | .node children => MathlibPlus.Open.RootedBoundaryLayers.forestBoundary children

/-- The connected rooted-boundary polynomial on the actual rooted-tree carrier.
It is the canonical `B_R` already defined by the finite rooted boundary
recursion. -/
noncomputable def connectedRootedBoundary (R : RTree) : BPoly :=
  MathlibPlus.Open.RootedBoundaryLayers.rootedBoundary R

/-- The `A_R` factor in the source specialization. -/
noncomputable def rootedBoundaryA (R : RTree) : BPoly :=
  childBoundaryProduct R

/-- Claim 49568: on every actual finite rooted-tree carrier, the connected
rooted-boundary recursion has the displayed specialization `B_R=v+r A_R`. -/
noncomputable def claim49568_connectedRootedBoundarySpecialization : Prop :=
  ∀ R : RTree,
    connectedRootedBoundary R =
      MathlibPlus.Open.RootedBoundaryLayers.vCoefficient +
        MathlibPlus.Open.RootedBoundaryLayers.zVariable * rootedBoundaryA R

end MathlibPlus.Open.ResearchFormalization.Claim49568
