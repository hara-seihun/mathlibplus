import Mathlib

namespace MathlibPlus.Analysis.Claim4666

open Complex Real

/-- The positive part of the real Jacobi theta series, indexed by `m ≥ 1`. -/
private noncomputable def thetaTail (u : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))

/-- The real theta series obtained from Jacobi's complex theta function. -/
private noncomputable def theta (y : ℝ) : ℝ :=
  (jacobiTheta ((y : ℂ) * I)).re

private theorem real_part_theta_term (u : ℝ) (n : ℕ) :
    (cexp (π * I * ((n : ℂ) + 1) ^ 2 * ((Real.exp (2 * u) : ℂ) * I))).re =
      Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) := by
  have hnre : (((n : ℂ) + 1) ^ 2).re = ((n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [pow_two, Complex.mul_re]
    norm_num
    ring
  have hnim : (((n : ℂ) + 1) ^ 2).im = 0 := by
    rw [pow_two, Complex.mul_im]
    norm_num
  have hure : ((cexp (2 * (u : ℂ))).re) = Real.exp (2 * u) := by
    rw [Complex.exp_re]
    simp
  have huim : ((cexp (2 * (u : ℂ))).im) = 0 := by
    rw [Complex.exp_im]
    simp
  let z : ℂ := π * I * ((n : ℂ) + 1) ^ 2 * ((Real.exp (2 * u) : ℂ) * I)
  have hzre : z.re = -Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) := by
    dsimp [z]
    rw [Complex.mul_re, Complex.mul_re]
    simp [Complex.mul_re, Complex.mul_im]
    rw [hnre, hnim, hure, huim]
    push_cast
    ring
  have hzim : z.im = 0 := by
    dsimp [z]
    rw [Complex.mul_im, Complex.mul_im]
    simp [Complex.mul_re, Complex.mul_im]
    rw [hnre, hnim, hure, huim]
    ring
  change (cexp z).re = _
  rw [Complex.exp_re, hzre, hzim]
  simp

/-- The theta series splits into its zero term and its two symmetric positive
and negative tails.  This is the exact orbit decomposition in claim 4666. -/
theorem theta_orbit_decomposition_claim4666 (u : ℝ) :
    theta (Real.exp (2 * u)) = 1 + 2 * thetaTail u := by
  rw [theta, thetaTail]
  have hτ : 0 < im ((Real.exp (2 * u) : ℂ) * I) := by
    rw [Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.I_im,
      Complex.I_re, mul_one, mul_zero, add_zero]
    exact Real.exp_pos _
  rw [jacobiTheta_eq_tsum_nat hτ]
  have hs : Summable (fun n : ℕ =>
      cexp (π * I * ((n : ℂ) + 1) ^ 2 * ((Real.exp (2 * u) : ℂ) * I))) :=
    (hasSum_nat_jacobiTheta hτ).summable
  rw [Complex.add_re, Complex.mul_re, Complex.re_tsum hs]
  norm_num
  apply tsum_congr
  intro n
  simpa using real_part_theta_term u n

end MathlibPlus.Analysis.Claim4666
