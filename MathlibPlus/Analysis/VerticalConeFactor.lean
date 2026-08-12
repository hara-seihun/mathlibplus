import Mathlib

namespace MathlibPlus.Analysis.VerticalConeFactor

/-- Claim 42861 (legacy packet R-2622): the exact strict-contraction threshold
for one paired complex Hadamard factor at a nonzero real height. -/
theorem exactVerticalConeThreshold_claim42861
    {ρ : ℂ} (hρ : ρ ≠ 0) {h : ℝ} (hh : h ≠ 0) :
    ‖1 + (h : ℂ) ^ 2 / ρ ^ 2‖ < 1 ↔
      h ^ 2 < 2 * (ρ.im ^ 2 - ρ.re ^ 2) := by
  have hn : 0 < Complex.normSq ρ := (Complex.normSq_pos).2 hρ
  have hn2 : 0 < Complex.normSq (ρ ^ 2) := by
    rw [map_pow]
    positivity
  have hρ2 : ρ ^ 2 ≠ 0 := pow_ne_zero 2 hρ
  have hrewrite :
      1 + (h : ℂ) ^ 2 / ρ ^ 2 = (ρ ^ 2 + (h : ℂ) ^ 2) / ρ ^ 2 := by
    field_simp
  rw [hrewrite]
  rw [← (sq_lt_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))]
  rw [Complex.sq_norm, Complex.normSq_div, Complex.normSq_apply]
  rw [div_lt_iff₀ hn2]
  rw [Complex.normSq_apply]
  simp only [pow_two]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  constructor <;> intro hineq
  · nlinarith [sq_pos_of_ne_zero hh]
  · nlinarith [sq_pos_of_ne_zero hh]

end MathlibPlus.Analysis.VerticalConeFactor
