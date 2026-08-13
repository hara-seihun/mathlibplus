import Mathlib

namespace MathlibPlus.Analysis.Claim12710

/-!
The positive imaginary axis is parametrized by `τ=iβ/(2π)`, so that the
standard nome `exp (2π i τ)` is `exp (-β)`.  The two theorems make both
conventions in the source claim explicit.
-/

/-- On the positive imaginary torus axis, modular `S` sends the inverse
temperature `β` to `4π²/β`. -/
theorem modularS_inverseTemperature_claim12710 (β : ℝ) (hβ : 0 < β) :
    let τ : ℂ := Complex.I * (β : ℂ) / (2 * Real.pi)
    let τS : ℂ := -1 / τ
    τS = Complex.I * ((4 * Real.pi ^ 2 / β : ℝ) : ℂ) / (2 * Real.pi) := by
  dsimp
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hβ)
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt Real.pi_pos)
  field_simp [hβc, hpi]
  rw [Complex.I_sq]
  norm_num
  field_simp [hβc]

/-- With the same parametrization, the standard nome is `e^(-β)`. -/
theorem nome_on_positive_imaginary_axis_claim12710 (β : ℝ) :
    let τ : ℂ := Complex.I * (β : ℂ) / (2 * Real.pi)
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ) =
      (Real.exp (-β) : ℂ) := by
  dsimp
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt Real.pi_pos)
  rw [Complex.ofReal_exp]
  congr 1
  field_simp [hpi]
  rw [Complex.I_sq]
  simp

end MathlibPlus.Analysis.Claim12710
