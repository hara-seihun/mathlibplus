import Mathlib

namespace MathlibPlus.Algebra.ReciprocalOffUnitQuadratic

/-- Claim 10616: the positive reciprocal quadratic has the displayed
factorization and exactly the two displayed roots. -/
theorem reciprocalOffUnitQuadratic
    (r : ℝ) (hr : 0 < r) (hr1 : r ≠ 1) :
    (∀ q : ℝ, r * q ^ 2 + (1 + r ^ 2) * q + r =
      (r * q + 1) * (q + r)) ∧
      (∀ q : ℝ,
        r * q ^ 2 + (1 + r ^ 2) * q + r = 0 ↔
          q = -r ∨ q = -(1 / r)) ∧
      0 > -r ∧ 0 > -(1 / r) ∧
      (-r) * (-(1 / r)) = 1 ∧
      ‖(-r : ℂ)‖ ≠ 1 ∧ ‖(-(1 / r : ℝ) : ℂ)‖ ≠ 1 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hinvpos : 0 < (1 / r : ℝ) := one_div_pos.mpr hr
  have hinv1 : (1 / r : ℝ) ≠ 1 := by
    intro h
    apply hr1
    field_simp [hr0] at h
    exact h.symm
  have hfactor : ∀ q : ℝ,
      r * q ^ 2 + (1 + r ^ 2) * q + r = (r * q + 1) * (q + r) := by
    intro q
    ring
  refine ⟨hfactor, ?_, by linarith, by linarith, ?_, ?_, ?_⟩
  · intro q
    constructor
    · intro hq
      rw [hfactor q] at hq
      rcases mul_eq_zero.mp hq with hq | hq
      · right
        have hq' : q = (-1 : ℝ) / r := by
          apply (eq_div_iff hr0).2
          nlinarith [hq]
        simpa [neg_div] using hq'
      · left
        linarith
    · rintro (rfl | rfl)
      · rw [hfactor]
        ring
      · rw [hfactor]
        field_simp [hr0]
        ring
  · field_simp [hr0]
  · rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact hr1
  · rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hinvpos]
    exact hinv1

end MathlibPlus.Algebra.ReciprocalOffUnitQuadratic
