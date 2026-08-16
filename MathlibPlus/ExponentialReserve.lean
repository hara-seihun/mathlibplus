import Mathlib

/-!
# Exponential endpoint reserve inequalities

Exact scalar reserve inequalities extracted from Records 5 and 6 of source record
`C-0179`.
-/

namespace MathlibPlus.ExponentialReserve

/-- If the logarithmic support fraction obeys `θ * (η + 1/2) < 1`, then both the
source exponent and every fixed subcritical-strip transform exponent from packet
`C-0179` are negative. -/
theorem exponents_negative
    (η θ : ℝ) (_hη : 0 ≤ η) (hθ : 0 < θ)
    (hreserve : θ * (η + 1 / 2) < 1) :
    -5 / 4 + θ * (η + 1 / 2) < 0 ∧
      ∀ Y : ℝ, Y < 1 / 2 →
        -5 / 4 + θ * η + θ * Y + Y / 2 < 0 := by
  constructor
  · linarith
  · intro Y hY
    have hθY : θ * Y < θ * (1 / 2 : ℝ) :=
      mul_lt_mul_of_pos_left hY hθ
    have hYhalf : Y / 2 < (1 : ℝ) / 4 := by linarith
    nlinarith

/-- At height `η = 1/2`, every positive logarithmic support fraction below one
satisfies the reserve criterion. -/
theorem halfHeight_reserve (θ : ℝ) (_hθ : 0 < θ) (hθone : θ < 1) :
    θ * ((1 / 2 : ℝ) + 1 / 2) < 1 := by
  norm_num at ⊢
  exact hθone

end MathlibPlus.ExponentialReserve
