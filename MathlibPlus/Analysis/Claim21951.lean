import Mathlib

namespace MathlibPlus.Analysis.Claim21951

/-- Claim 21951: the exact two-factor product-error inequality. -/
theorem twoFactorProductError (M A rM rA : ℂ) :
    ‖(M + rM) * (A + rA) - M * A‖ ≤
      ‖rM‖ * ‖A‖ + ‖rA‖ * ‖M‖ + ‖rM‖ * ‖rA‖ := by
  calc
    ‖(M + rM) * (A + rA) - M * A‖ =
        ‖rM * A + M * rA + rM * rA‖ := by
      congr 1
      ring
    _ ≤ ‖rM * A‖ + ‖M * rA‖ + ‖rM * rA‖ := by
      calc
        ‖rM * A + M * rA + rM * rA‖ =
            ‖rM * A + (M * rA + rM * rA)‖ := by
          congr 1
          ring
        _ ≤ ‖rM * A‖ + ‖M * rA + rM * rA‖ :=
          norm_add_le (rM * A) (M * rA + rM * rA)
        _ ≤ ‖rM * A‖ + (‖M * rA‖ + ‖rM * rA‖) := by
          exact add_le_add_right (norm_add_le (M * rA) (rM * rA)) _
        _ = ‖rM * A‖ + ‖M * rA‖ + ‖rM * rA‖ := by ring
    _ = ‖rM‖ * ‖A‖ + ‖rA‖ * ‖M‖ + ‖rM‖ * ‖rA‖ := by
      rw [norm_mul, norm_mul, norm_mul]
      ring

end MathlibPlus.Analysis.Claim21951
