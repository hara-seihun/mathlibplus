import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace MathlibPlus.Analysis.Claim14173

/-- The finite-difference kernel is nonnegative on the nonnegative real axis
and vanishes at the origin. -/
theorem finiteDifference_kernel_properties_claim14173 (h : ℝ)
    (hh : 0 ≤ h) :
    (let f_h : ℝ → ℝ := fun u => 1 - Real.exp (-h * u)
     f_h 0 = 0 ∧ ∀ u, 0 ≤ u → 0 ≤ f_h u) := by
  dsimp
  constructor
  · simp
  · intro u hu
    have hprod : 0 ≤ h * u := mul_nonneg hh hu
    have he : Real.exp (-h * u) ≤ 1 :=
      (Real.exp_le_one_iff).2 (by linarith)
    linarith

/-- Exact real part of the gamma-canceling finite difference away from its poles. -/
theorem finiteDifference_realPart_claim14173 (h x y : ℝ)
    (hz : (x : ℂ) + (y : ℂ) * Complex.I ≠ 0)
    (hzh : (x : ℂ) + (y : ℂ) * Complex.I + (h : ℂ) ≠ 0) :
    ((1 / ((x : ℂ) + (y : ℂ) * Complex.I) -
        1 / ((x : ℂ) + (y : ℂ) * Complex.I + (h : ℂ))).re) =
      h * (x * (x + h) - y ^ 2) /
        ((x ^ 2 + y ^ 2) * ((x + h) ^ 2 + y ^ 2)) := by
  let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  have hz' : z ≠ 0 := by simpa [z] using hz
  have hzh' : z + (h : ℂ) ≠ 0 := by simpa [z] using hzh
  have hid : 1 / z - 1 / (z + (h : ℂ)) =
      (h : ℂ) / (z * (z + (h : ℂ))) := by
    field_simp [hz', hzh']
    ring
  rw [show (x : ℂ) + (y : ℂ) * Complex.I = z by rfl]
  rw [show (x : ℂ) + (y : ℂ) * Complex.I + (h : ℂ) =
    z + (h : ℂ) by rfl]
  have hreal : (z * (z + (h : ℂ))).re = x * (x + h) - y ^ 2 := by
    simp [z, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hnorm : Complex.normSq (z * (z + (h : ℂ))) =
      (x ^ 2 + y ^ 2) * ((x + h) ^ 2 + y ^ 2) := by
    rw [map_mul, Complex.normSq_apply, Complex.normSq_apply]
    simp [z, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hid, Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
  rw [hreal, hnorm]

/-- The real part changes sign in the stated region. -/
theorem finiteDifference_realPart_negative_claim14173 (h x y : ℝ)
    (hh : 0 < h)
    (hz : (x : ℂ) + (y : ℂ) * Complex.I ≠ 0)
    (hzh : (x : ℂ) + (y : ℂ) * Complex.I + (h : ℂ) ≠ 0)
    (hy : y ^ 2 > x * (x + h)) :
    ((1 / ((x : ℂ) + (y : ℂ) * Complex.I) -
        1 / ((x : ℂ) + (y : ℂ) * Complex.I + (h : ℂ))).re) < 0 := by
  rw [finiteDifference_realPart_claim14173 h x y hz hzh]
  have hp : 0 < (x ^ 2 + y ^ 2) * ((x + h) ^ 2 + y ^ 2) := by
    have h1 : 0 < x ^ 2 + y ^ 2 := by
      have hnorm := (Complex.normSq_pos).2 hz
      simpa [Complex.normSq_apply, pow_two] using hnorm
    have h2 : 0 < (x + h) ^ 2 + y ^ 2 := by
      have hnorm := (Complex.normSq_pos).2 hzh
      simpa [Complex.normSq_apply, pow_two] using hnorm
    positivity
  have hn : h * (x * (x + h) - y ^ 2) < 0 := by
    nlinarith
  exact div_neg_of_neg_of_pos hn hp

end MathlibPlus.Analysis.Claim14173
