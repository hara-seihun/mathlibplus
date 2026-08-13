import Mathlib

namespace MathlibPlus.LinearAlgebra.LeafExtensionTanner

/-- The dual common kernel from claim 5142.  The packet's card-specific
vertex sets, attachment map, and feature coordinates are explicit parameters;
the formula therefore does not add an ambient graph or coefficient-domain
hypothesis. -/
noncomputable def dualCommonKernel
    {Card Target Feature Vertex R : Type*} [CommSemiring R]
    (vertices : Card → Finset Vertex)
    (attach : Card → Vertex → Target)
    (feature : Card → Feature → Vertex → R) : Set (Target → R) :=
  {a | ∀ C f, (∑ v ∈ vertices C, feature C f v * a (attach C v)) = 0}

end MathlibPlus.LinearAlgebra.LeafExtensionTanner
