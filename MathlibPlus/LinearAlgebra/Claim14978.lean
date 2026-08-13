import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- Any `m+1` homogeneous linear constraints on `m+2` coefficients have a
nonzero simultaneous solution.  This is the linear-algebra core of claim
14978; the source-specific carrier and integral maps are not part of this
abstract statement. -/
theorem claim14978_nontrivial_kernel
    (m : ℕ) (f : (Fin (m + 2) → ℚ) →ₗ[ℚ] (Fin (m + 1) → ℚ)) :
    ∃ c : Fin (m + 2) → ℚ, c ≠ 0 ∧ f c = 0 := by
  have hdim : Module.finrank ℚ (Fin (m + 1) → ℚ) <
      Module.finrank ℚ (Fin (m + 2) → ℚ) := by
    simp [Module.finrank_fintype_fun_eq_card]
  have hker : LinearMap.ker f ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨c, hc0, hc⟩

end MathlibPlus.LinearAlgebra
