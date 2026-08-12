import Mathlib

namespace MathlibPlus.Analysis.Claim17995

open scoped InnerProductSpace

/-- Claim 17995: a hyperbolic unit-vector combination of an orthonormal pair. -/
theorem hyperbolicUnitVector_norm_claim17995
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e n : E) (he : ‖e‖ = 1) (hn : ‖n‖ = 1)
    (hen : ⟪e, n⟫_ℝ = 0) (ξ : ℝ) :
    ‖Real.tanh ξ • e + (1 / Real.cosh ξ) • n‖ = 1 := by
  have hcosh : Real.cosh ξ ≠ 0 := (Real.cosh_pos ξ).ne'
  have hhyper : (Real.tanh ξ) ^ 2 + (Real.cosh ξ ^ 2)⁻¹ = 1 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq ξ]
  have hnormsq :
      ‖Real.tanh ξ • e + (1 / Real.cosh ξ) • n‖ ^ 2 = 1 := by
    rw [norm_add_sq_real]
    simp [norm_smul, he, hn, real_inner_smul_left, real_inner_smul_right, hen]
    exact hhyper
  nlinarith [norm_nonneg (Real.tanh ξ • e + (1 / Real.cosh ξ) • n)]

end MathlibPlus.Analysis.Claim17995
