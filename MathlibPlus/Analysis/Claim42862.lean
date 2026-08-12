import Mathlib

namespace MathlibPlus.Analysis.Claim42862

/-- Claim 42862: the exact strict-contraction threshold for a paired complex
Hadamard factor, including the necessary height-zero degeneracy. -/
theorem exactVerticalConeThreshold
    {ρ : ℂ} (hρ : ρ ≠ 0) {h : ℝ} :
    ‖1 + (h : ℂ) ^ 2 / ρ ^ 2‖ < 1 ↔
      h ≠ 0 ∧ h ^ 2 < 2 * (ρ.im ^ 2 - ρ.re ^ 2) := by
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
  constructor
  · intro hineq
    have hh : h ≠ 0 := by
      intro hz
      subst h
      norm_num at hineq
    exact ⟨hh, by nlinarith [sq_pos_of_ne_zero hh]⟩
  · rintro ⟨hh, hineq⟩
    nlinarith [sq_pos_of_ne_zero hh]

/-- Claim 42863: at a fixed nonzero height, the same threshold can be
written as the strict hyperbolic location inequality. -/
theorem verticalConeLocationCriterion
    {ρ : ℂ} (hρ : ρ ≠ 0) {h : ℝ} (hh : h ≠ 0) :
    ‖1 + (h : ℂ) ^ 2 / ρ ^ 2‖ < 1 ↔
      ρ.im ^ 2 - ρ.re ^ 2 > h ^ 2 / 2 := by
  rw [exactVerticalConeThreshold hρ]
  constructor
  · rintro ⟨_, hineq⟩
    nlinarith
  · intro hineq
    exact ⟨hh, by nlinarith⟩

end MathlibPlus.Analysis.Claim42862
