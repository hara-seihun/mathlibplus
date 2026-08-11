import Mathlib

/-!
# Cayley coordinates of complex zeros

This file formalizes the two elementary Cayley-coordinate identities in Records 2
and 3 of legacy packet `D-0032`.  It makes no claim about the zero set of the
Riemann zeta function and does not interpret the packet's regularized Li sum.
-/

namespace MathlibPlus.Complex.CayleyZero

/-- The Cayley coordinate `1 - 1 / ρ` lies on the unit circle exactly when `ρ`
lies on the vertical line of real part `1/2`. -/
theorem norm_one_sub_inv_eq_one_iff (ρ : ℂ) (hρ : ρ ≠ 0) :
    ‖1 - 1 / ρ‖ = 1 ↔ ρ.re = (1 : ℝ) / 2 := by
  rw [show (1 - 1 / ρ : ℂ) = (ρ - 1) / ρ by field_simp]
  rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hρ)]
  constructor
  · intro h
    have hsq : ‖ρ - 1‖ ^ 2 = ‖ρ‖ ^ 2 := congrArg (fun x : ℝ => x ^ 2) h
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply] at hsq
    norm_num at hsq ⊢
    linarith
  · intro h
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply]
    norm_num at h ⊢
    linarith

/-- The functional-equation partner `1 - ρ` has reciprocal Cayley coordinate. -/
theorem one_sub_inv_one_sub (ρ : ℂ) (hρ : ρ ≠ 0) (hρ1 : ρ ≠ 1) :
    1 - 1 / (1 - ρ) = (1 - 1 / ρ)⁻¹ := by
  field_simp
  ring

end MathlibPlus.Complex.CayleyZero
