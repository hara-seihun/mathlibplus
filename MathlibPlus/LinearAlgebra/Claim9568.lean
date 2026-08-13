import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim9568

/-- An isometry cannot have a nonzero eigenvector with an eigenvalue of modulus
other than one. This is the positive-metric implication isolated from claim
9568's multiplication-by-`u` setting. -/
theorem unitaryEigenvalue_modulus_one_claim9568
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {T : V →ₗ[ℂ] V} (hT : Isometry T)
    {v : V} {eig : ℂ} (hv : v ≠ 0) (he : T v = eig • v) :
    ‖eig‖ = 1 := by
  have hnorm : ‖T v‖ = ‖v‖ := by
    simpa [dist_zero_right, T.map_zero] using hT.dist_eq v 0
  rw [he, norm_smul] at hnorm
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  nlinarith

end MathlibPlus.LinearAlgebra.Claim9568
