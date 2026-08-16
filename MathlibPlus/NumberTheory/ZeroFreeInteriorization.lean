import Mathlib

/-!
# Zero-free denominator interiorization

The exact order-theoretic interiorization lemma extracted from source record `C-0098`.
It is parameterized by the complex-valued function and asserts no zeta theorem itself.
-/

namespace MathlibPlus.NumberTheory.ZeroFreeInteriorization

/-- Enlarging a positive zero-free denominator moves the corresponding closed boundary
strictly inside the region supplied by the smaller open denominator. -/
theorem openToClosedDenominator
    (zeta : ℂ → ℂ) (R₀ R₁ t : ℝ)
    (hR₀ : 0 < R₀) (hR : R₀ < R₁) (ht : 1 < t)
    (hopen : ∀ σ : ℝ, 1 - 1 / (R₀ * Real.log t) < σ →
      zeta (σ + t * Complex.I) ≠ 0) :
    ∀ σ : ℝ, 1 - 1 / (R₁ * Real.log t) ≤ σ →
      zeta (σ + t * Complex.I) ≠ 0 := by
  have hlog : 0 < Real.log t := Real.log_pos ht
  have hden₀ : 0 < R₀ * Real.log t := mul_pos hR₀ hlog
  have hden : R₀ * Real.log t < R₁ * Real.log t :=
    mul_lt_mul_of_pos_right hR hlog
  have hrecip : 1 / (R₁ * Real.log t) < 1 / (R₀ * Real.log t) :=
    one_div_lt_one_div_of_lt hden₀ hden
  intro σ hσ
  apply hopen σ
  linarith

end MathlibPlus.NumberTheory.ZeroFreeInteriorization
