import Mathlib

namespace MathlibPlus.Analysis.Claim42868

/-- Reciprocal Gamma vanishes at the non-positive integer induced by a positive odd center;
the reflection-side cosine factor vanishes at the same center. -/
theorem reciprocalGammaReflectionIdentity (n : ℕ) :
    (Complex.Gamma ((1 - (2 * n + 1)) / 2))⁻¹ =
        Complex.Gamma ((1 + (2 * n + 1)) / 2) *
          Complex.cos ((Real.pi : ℂ) * (2 * n + 1) / 2) / (Real.pi : ℂ) ∧
      (Complex.Gamma ((1 - (2 * n + 1)) / 2))⁻¹ = 0 ∧
        Complex.Gamma ((1 + (2 * n + 1)) / 2) *
          Complex.cos ((Real.pi : ℂ) * (2 * n + 1) / 2) / (Real.pi : ℂ) = 0 := by
  have hneg : ((1 - (2 * n + 1)) / 2 : ℂ) = -(n : ℂ) := by
    push_cast
    ring
  have hcos : Complex.cos ((Real.pi : ℂ) * (2 * n + 1) / 2) = 0 := by
    have hreal : Real.cos (Real.pi * (2 * n + 1) / 2) = 0 := by
      rw [show (Real.pi * (2 * n + 1) / 2 : ℝ) =
          (Real.pi / 2 + n * Real.pi) by
        push_cast
        ring]
      rw [Real.cos_add_nat_mul_pi]
      simp
    have harg : ((Real.pi : ℂ) * (2 * n + 1) / 2) =
        (Real.pi * (2 * n + 1) / 2 : ℝ) := by
      push_cast
      ring
    rw [harg, ← Complex.ofReal_cos]
    exact_mod_cast hreal
  rw [hneg, Complex.Gamma_neg_nat_eq_zero, inv_zero, hcos]
  simp

end MathlibPlus.Analysis.Claim42868
