import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim7764

/-- Claim 7764, half-parameter signed recovery. Here `x` is the `AI` term and
`y` is the `CS` term, so this is the componentwise identity for matrices or any
real module. -/
theorem signedRecovery_half {V : Type*} [AddCommGroup V] [Module ℝ V]
    (x y : V) :
    x + y = (2 : ℝ) • (x + (1 / 2 : ℝ) • y) - x := by
  module

/-- Claim 7764, the general nonzero-parameter recovery identity. -/
theorem signedRecovery_general {V : Type*} [AddCommGroup V] [Module ℝ V]
    (x y : V) (l : ℝ) (hl : l ≠ 0) :
    x + y = l⁻¹ • (x + l • y) - (l⁻¹ - 1) • x := by
  rw [smul_add, smul_smul, inv_mul_cancel₀ hl]
  module

/-- The coefficient `2` in the half-parameter recovery forces the parameter to
be `1/2`. -/
theorem coefficient_two_forces_half (l : ℝ) (h : l⁻¹ = 2) :
    l = 1 / 2 := by
  have hl : l ≠ 0 := by
    intro hl
    subst l
    norm_num at h
  field_simp [hl] at h ⊢
  linarith

end MathlibPlus.LinearAlgebra.Claim7764
