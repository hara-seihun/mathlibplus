import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim7949

/-- The commutation relation `d τ_j = τ_(j-1) d` turns the difference of
successive operators `I - p^(-j/2) τ_j` into the claimed curvature term.  The
half-integral powers are Lean's real `rpow`s. -/
theorem curvedDegreeLadder_claim7949
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : ℝ) (j : ℕ) (hj : 0 < j)
    (d : V →ₗ[ℝ] V) (τ : ℕ → V →ₗ[ℝ] V)
    (hcomm : d.comp (τ j) = (τ (j - 1)).comp d)
    (hp : 0 < p) :
    d.comp (LinearMap.id - (p ^ (-(j : ℝ) / 2)) • τ j) -
        (LinearMap.id - (p ^ (-((j - 1 : ℕ) : ℝ) / 2)) • τ (j - 1)).comp d =
      ((p ^ (-((j - 1 : ℕ) : ℝ) / 2)) *
          (1 - p ^ (-(1 : ℝ) / 2))) • ((τ (j - 1)).comp d) := by
  have hcast : (j : ℝ) = ((j - 1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub hj]
    norm_num
  have hpow : p ^ (-(j : ℝ) / 2) =
      p ^ (-((j - 1 : ℕ) : ℝ) / 2) * p ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_add hp]
    congr 1
    rw [hcast]
    ring
  simp only [LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_id,
    LinearMap.id_comp, LinearMap.comp_smul, LinearMap.smul_comp]
  rw [hcomm, hpow]
  module

end MathlibPlus.LinearAlgebra.Claim7949
