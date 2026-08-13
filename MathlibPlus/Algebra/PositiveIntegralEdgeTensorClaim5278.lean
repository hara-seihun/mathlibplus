import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

namespace MathlibPlus.Algebra

open scoped TensorProduct

/-- Positive integer indices used for integral edge lengths. -/
abbrev PositiveEdgeLength := {n : ℕ // 0 < n}

/-- The free rational vector space on positive integral edge lengths. -/
abbrev PositiveEdgeLengthSpace := PositiveEdgeLength →₀ ℚ

/-- The basis vector indexed by a positive integral edge length. -/
noncomputable def positiveEdgeVector (ℓ : PositiveEdgeLength) : PositiveEdgeLengthSpace :=
  Finsupp.single ℓ 1

/-- The canonical basis of the free rational edge-length space. -/
noncomputable def positiveEdgeBasis :
    Module.Basis PositiveEdgeLength ℚ PositiveEdgeLengthSpace :=
  Finsupp.basisSingleOne

/-- The ordered tensor basis indexed by ordered pairs of positive lengths. -/
noncomputable def orderedPositiveEdgeTensorBasis :
    Module.Basis (PositiveEdgeLength × PositiveEdgeLength) ℚ
      (PositiveEdgeLengthSpace ⊗[ℚ] PositiveEdgeLengthSpace) :=
  positiveEdgeBasis.tensorProduct positiveEdgeBasis

end MathlibPlus.Algebra
