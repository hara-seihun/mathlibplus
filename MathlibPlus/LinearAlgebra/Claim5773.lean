import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra.Claim5773

/-- Rank-nullity written as the column deficiency of a finite-dimensional
observation map, as in the Kelly-kernel claim. -/
theorem kelly_kernel_finrank_deficiency_claim5773
    {K V W : Type*} [DivisionRing K]
    [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W] [FiniteDimensional K V]
    (Φ : V →ₗ[K] W) :
    Module.finrank K (LinearMap.ker Φ) =
      Module.finrank K V - Module.finrank K (LinearMap.range Φ) := by
  have h := LinearMap.finrank_range_add_finrank_ker Φ
  omega

end MathlibPlus.LinearAlgebra.Claim5773
