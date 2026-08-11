import MathlibPlus.Basic

namespace MathlibPlus.Complex

/-- The exact real/imaginary-coordinate consequences of the xi-zero map
`z = (u + i*gamma)^2`. -/
theorem xiZeroMap_coordinates (u γ : ℝ) :
    let z : ℂ := ((u : ℂ) + Complex.I * (γ : ℂ)) ^ 2
    (u = 0 → z = -(γ : ℂ) ^ 2) ∧
      (u ≠ 0 → γ ≠ 0 → z.im ≠ 0) := by
  dsimp
  constructor
  · intro hu
    subst u
    apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im]
  · intro hu hγ hz
    have him : (((u : ℂ) + Complex.I * (γ : ℂ)) ^ 2).im = 2 * u * γ := by
      simp [pow_two, Complex.mul_im, Complex.add_im, Complex.I_mul_I]
      ring
    rw [him] at hz
    exact (mul_ne_zero (mul_ne_zero (by norm_num) hu) hγ) hz

/-- Conjugating the mapped point changes the sign of the ordinate and hence
produces the conjugate point in the `z`-plane. -/
theorem xiZeroMap_conjugate (u γ : ℝ) :
    starRingEnd ℂ (((u : ℂ) + Complex.I * (γ : ℂ)) ^ 2) =
      ((u : ℂ) - Complex.I * (γ : ℂ)) ^ 2 := by
  rw [map_pow]
  congr 1
  simp
  ring

end MathlibPlus.Complex
