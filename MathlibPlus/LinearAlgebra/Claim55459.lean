import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra.Claim55459

/-- The finite-measurement rank-nullity bound from R-4923.3 (claim 55459).
The carrier has the literal dimensions from the preceding records, while the
map is represented by its complex-linear measurement map. -/
theorem finiteMeasurementKernelDimension_claim55459
    {R M : ℕ} (hR : R = 5660573696) (hM : M = 32768)
    (L : (Fin R → ℂ) →ₗ[ℂ] (Fin (2 * M) → ℂ)) :
    5660508160 ≤ Module.finrank ℂ (LinearMap.ker L) ∧
      0 < Module.finrank ℂ (LinearMap.ker L) := by
  have hdim := LinearMap.finrank_range_add_finrank_ker L
  have hrange : Module.finrank ℂ (LinearMap.range L) ≤ 2 * M := by
    simpa using (LinearMap.range L).finrank_le
  have hdim' : Module.finrank ℂ (LinearMap.range L) +
      Module.finrank ℂ (LinearMap.ker L) = R := by
    simpa using hdim
  have hbound : R - 2 * M ≤ Module.finrank ℂ (LinearMap.ker L) := by
    omega
  constructor <;> omega

end MathlibPlus.LinearAlgebra.Claim55459
