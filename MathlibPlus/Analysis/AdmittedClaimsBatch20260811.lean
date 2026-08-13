import Mathlib

namespace MathlibPlus.Analysis.AdmittedClaimsBatch20260811

/-- Claim 14266: the displayed cosine multiplier is the negative square of
its sine form, and hence is nonpositive on the real axis. -/
theorem claim14266_sineSquareMultiplier :
    (∀ z : Complex,
      (Complex.cos (2 * (Real.pi : Complex) * Complex.exp z) - 1) / 2 =
        -(Complex.sin ((Real.pi : Complex) * Complex.exp z)) ^ 2) ∧
      (∀ t : ℝ,
        (Real.cos (2 * Real.pi * Real.exp t) - 1) / 2 ≤ 0) := by
  constructor
  · intro z
    rw [show 2 * (Real.pi : Complex) * Complex.exp z =
        2 * ((Real.pi : Complex) * Complex.exp z) by ring]
    rw [Complex.cos_two_mul_eq_one_sub]
    ring
  · intro t
    have h : (Real.cos (2 * Real.pi * Real.exp t) - 1) / 2 =
        -(Real.sin (Real.pi * Real.exp t)) ^ 2 := by
      rw [show 2 * Real.pi * Real.exp t =
          2 * (Real.pi * Real.exp t) by ring]
      rw [Real.cos_two_mul_eq_one_sub]
      ring
    rw [h]
    nlinarith [sq_nonneg (Real.sin (Real.pi * Real.exp t))]

/-- Claim 44177: exponential nodes factor over an additive split. -/
theorem claim44177_exponentialNodeFactorization (lam θ u v : Complex) :
    Complex.exp ((-lam + Complex.I * θ) * (u + v)) =
      Complex.exp ((-lam + Complex.I * θ) * u) *
        Complex.exp ((-lam + Complex.I * θ) * v) := by
  rw [mul_add, Complex.exp_add]

end MathlibPlus.Analysis.AdmittedClaimsBatch20260811
