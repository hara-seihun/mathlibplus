import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

namespace MathlibPlus.Analysis.Claim18826

/-- For positive real part, the real part of complex `tanh` dominates its
real-axis value wherever the complex denominator is nonzero. -/
theorem realPart_tanh_ge_claim18826 (X : ℝ) (hX : 0 < X) (T : ℝ)
    (hcosh : Complex.cosh ((X : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    (Complex.tanh ((X : ℂ) + (T : ℂ) * Complex.I)).re ≥ Real.tanh X := by
  have hsinh_re :
      (Complex.sinh ((X : ℂ) + (T : ℂ) * Complex.I)).re =
        Real.sinh X * Real.cos T := by
    rw [Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I]
    simp [Complex.mul_re, Complex.mul_im, Complex.sinh_ofReal_re,
      Complex.sinh_ofReal_im, Complex.cosh_ofReal_re, Complex.cosh_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_re,
      Complex.cos_ofReal_im]
  have hsinh_im :
      (Complex.sinh ((X : ℂ) + (T : ℂ) * Complex.I)).im =
        Real.cosh X * Real.sin T := by
    rw [Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I]
    simp [Complex.mul_re, Complex.mul_im, Complex.sinh_ofReal_re,
      Complex.sinh_ofReal_im, Complex.cosh_ofReal_re, Complex.cosh_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_re,
      Complex.cos_ofReal_im]
  have hcosh_re :
      (Complex.cosh ((X : ℂ) + (T : ℂ) * Complex.I)).re =
        Real.cosh X * Real.cos T := by
    rw [Complex.cosh_add, Complex.sinh_mul_I, Complex.cosh_mul_I]
    simp [Complex.mul_re, Complex.mul_im, Complex.sinh_ofReal_re,
      Complex.sinh_ofReal_im, Complex.cosh_ofReal_re, Complex.cosh_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_re,
      Complex.cos_ofReal_im]
  have hcosh_im :
      (Complex.cosh ((X : ℂ) + (T : ℂ) * Complex.I)).im =
        Real.sinh X * Real.sin T := by
    rw [Complex.cosh_add, Complex.sinh_mul_I, Complex.cosh_mul_I]
    simp [Complex.mul_re, Complex.mul_im, Complex.sinh_ofReal_re,
      Complex.sinh_ofReal_im, Complex.cosh_ofReal_re, Complex.cosh_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_re,
      Complex.cos_ofReal_im]
  have htanh_re_formula :
      (Complex.tanh ((X : ℂ) + (T : ℂ) * Complex.I)).re =
        (Real.sinh X * Real.cosh X) /
          (Real.cosh X ^ 2 * Real.cos T ^ 2 +
            Real.sinh X ^ 2 * Real.sin T ^ 2) := by
    rw [Complex.tanh_eq_sinh_div_cosh, Complex.div_re,
      Complex.normSq_apply]
    simp only [hsinh_re, hsinh_im, hcosh_re, hcosh_im]
    have htrig : Real.cos T ^ 2 + Real.sin T ^ 2 = 1 := by
      nlinarith [Real.sin_sq_add_cos_sq T]
    calc
      _ = Real.sinh X * Real.cosh X *
          (Real.cos T ^ 2 + Real.sin T ^ 2) *
            (Real.sinh X ^ 2 * Real.sin T ^ 2 +
              Real.cos T ^ 2 * Real.cosh X ^ 2)⁻¹ := by ring
      _ = _ := by rw [htrig]; ring
  let den : ℝ := Real.cosh X ^ 2 * Real.cos T ^ 2 +
    Real.sinh X ^ 2 * Real.sin T ^ 2
  have hden_eq : den =
      Complex.normSq (Complex.cosh ((X : ℂ) + (T : ℂ) * Complex.I)) := by
    dsimp [den]
    rw [Complex.normSq_apply, hcosh_re, hcosh_im]
    ring
  have hden : 0 < den := by
    rw [hden_eq]
    exact (Complex.normSq_pos).2 hcosh
  have hsinh : 0 < Real.sinh X := (Real.sinh_pos_iff).2 hX
  have hcoshpos : 0 < Real.cosh X := Real.cosh_pos X
  rw [htanh_re_formula, Real.tanh_eq_sinh_div_cosh]
  apply (div_le_div_iff₀ hcoshpos hden).2
  have hden_le : den ≤ Real.cosh X ^ 2 := by
    dsimp [den]
    nlinarith [Real.sin_sq_add_cos_sq T, Real.sinh_sq X,
      sq_nonneg (Real.cos T), sq_nonneg (Real.sin T)]
  nlinarith

end MathlibPlus.Analysis.Claim18826
