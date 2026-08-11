import Mathlib

namespace MathlibPlus.Analysis.Claim13736

/-- Claim 13736: critical-line ratio formula. -/
theorem criticalLineRatioFormula (t τ : ℝ) :
    let s : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
    let ρ : ℂ := (1 / 2 : ℂ) + (τ : ℂ) * Complex.I
    ‖s * (1 - s) / (ρ * (1 - ρ))‖ =
      (1 / 4 + t ^ 2) / (1 / 4 + τ ^ 2) := by
  dsimp
  have ht : 0 < (1 / 4 + t ^ 2 : ℝ) := by positivity
  have hτ : 0 < (1 / 4 + τ ^ 2 : ℝ) := by positivity
  have hs : ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) *
        (1 - ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) =
      ((1 / 4 + t ^ 2 : ℝ) : ℂ) := by
    rw [show (1 : ℂ) - ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
        (1 / 2 : ℂ) - (t : ℂ) * Complex.I by ring]
    rw [Complex.ext_iff]
    constructor <;> norm_num [Complex.mul_re, Complex.mul_im, pow_two] <;> ring
  have hρ : ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I) *
        (1 - ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I)) =
      ((1 / 4 + τ ^ 2 : ℝ) : ℂ) := by
    rw [show (1 : ℂ) - ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I) =
        (1 / 2 : ℂ) - (τ : ℂ) * Complex.I by ring]
    rw [Complex.ext_iff]
    constructor <;> norm_num [Complex.mul_re, Complex.mul_im, pow_two] <;> ring
  rw [hs, hρ, norm_div, Complex.norm_real, Complex.norm_real]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht, abs_of_pos hτ]

end MathlibPlus.Analysis.Claim13736

namespace MathlibPlus.Analysis.Claim19168

/-- Claim 19168: the strict Schur-complement defect in the hyperbolic
parametrization `C = cosh ξ`, `S = sinh ξ`; `sech ξ` is `1 / cosh ξ`. -/
theorem strictSchurComplementDefect (ξ : ℝ) :
    let C := Real.cosh ξ
    let S := Real.sinh ξ
    C - S ^ 2 / C = 1 / C ∧
      0 < 1 / C ∧
      C - S ^ 2 / C = 1 / Real.cosh ξ := by
  dsimp
  have hC : 0 < Real.cosh ξ := Real.cosh_pos ξ
  have hC0 : Real.cosh ξ ≠ 0 := ne_of_gt hC
  have hident : Real.cosh ξ ^ 2 - Real.sinh ξ ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq ξ
  constructor
  · field_simp
    nlinarith
  constructor
  · positivity
  · field_simp [hC0]
    nlinarith [hident]

end MathlibPlus.Analysis.Claim19168
