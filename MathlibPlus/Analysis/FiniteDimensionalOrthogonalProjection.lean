import Mathlib

/-!
# Compactness of finite-dimensional orthogonal projections

Formalization of admitted claim 3916.  The projection is represented by
`Submodule.starProjection`, whose bundled type is a continuous linear map; the
result below proves its compact-operator property when the target subspace is
finite-dimensional.
-/

namespace MathlibPlus.Analysis.FiniteDimensionalOrthogonalProjection

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The orthogonal projection onto a finite-dimensional subspace is a compact operator.
The bundled map is a continuous linear map by construction. -/
theorem isCompactOperator_starProjection (K : Submodule 𝕜 E)
    [FiniteDimensional 𝕜 K] :
    IsCompactOperator K.starProjection := by
  rw [Submodule.starProjection]
  exact (isCompactOperator_of_locallyCompactSpace_dom K.orthogonalProjectionOnto).clm_comp
    K.subtypeL

end MathlibPlus.Analysis.FiniteDimensionalOrthogonalProjection
