import Mathlib

namespace MathlibPlus.Algebra.ClaimIdentities

/-- Claim 13800: exact exponent gap and its consequence below `η = 1`. -/
theorem exactExponentGap (δ η : ℝ) :
    ((1 + δ - η) - (δ - 1) = 2 - η) ∧
      (η < 1 →
        ((1 + δ - η) - (δ - 1) > 1 ∧ δ - 1 < 1 + δ - η)) := by
  constructor
  · ring
  · intro hη
    constructor <;> linarith

/-- Claim 15660: the slope/rate pair recovers the squared height. -/
theorem slopeAndRateRecoverSquaredHeight (β γ d κ : ℝ)
    (hd : d = 1 / ((β - 1) ^ 2 + γ ^ 2))
    (hd0 : d ≠ 0)
    (hκ : κ = (2 * β - 1) * d) :
    γ ^ 2 = 1 / d - (1 - κ / d) ^ 2 / 4 := by
  have hden : (β - 1) ^ 2 + γ ^ 2 ≠ 0 := by
    intro hden
    rw [hden] at hd
    norm_num at hd
    exact hd0 hd
  have hprod : d * ((β - 1) ^ 2 + γ ^ 2) = 1 := by
    rw [hd]
    field_simp [hden]
  rw [hκ]
  field_simp [hd0]
  nlinarith [hprod]

end MathlibPlus.Algebra.ClaimIdentities
