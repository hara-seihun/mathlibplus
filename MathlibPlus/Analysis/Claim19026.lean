import MathlibPlus.Basic

namespace MathlibPlus.Analysis

/-- The one-factor fugacity root and its modulus criterion. -/
theorem claim19026_root_unimodularity (q : ℝ) (hq : 0 < q) :
    let u : ℂ := -((q : ℂ)⁻¹)
    (1 + (q : ℂ) * u = 0) ∧
      (∀ v : ℂ, 1 + (q : ℂ) * v = 0 → v = u) ∧
      (‖u‖ = 1 ↔ q = 1) := by
  dsimp
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hq0c : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
  have hu : 1 + (q : ℂ) * -((q : ℂ)⁻¹) = 0 := by
    rw [mul_neg, mul_inv_cancel₀ hq0c]
    ring
  constructor
  · exact hu
  · constructor
    · intro v hv
      have hv' : (q : ℂ) * v = -1 := by linear_combination hv
      have hu' : (q : ℂ) * -((q : ℂ)⁻¹) = -1 := by
        rw [mul_neg, mul_inv_cancel₀ hq0c]
      exact mul_left_cancel₀ hq0c (hv'.trans hu'.symm)
    · rw [norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
      constructor
      · intro h
        have : q⁻¹ = (1 : ℝ) := by simpa using h
        exact inv_eq_one.mp this
      · intro h
        subst q
        norm_num

end MathlibPlus.Analysis
