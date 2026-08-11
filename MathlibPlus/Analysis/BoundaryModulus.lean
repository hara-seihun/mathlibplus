import Mathlib

namespace MathlibPlus.Analysis

open Complex

/-- Pointwise boundary factorization of the distance to `α`.  The radius is
assumed positive because the displayed factorization divides by `r^2`. -/
theorem boundaryModulusFactorization (w α : ℂ) (r : ℝ) (hr : 0 < r)
    (hw : ‖w‖ = r) :
    ‖w - α‖ = ‖(r : ℂ) * (1 - star α * w / (r : ℂ) ^ 2)‖ := by
  have hr0 : (r : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hr)
  have hww : w * star w = (r : ℂ) ^ 2 := by
    have h := Complex.mul_conj w
    simp only [starRingEnd_apply] at h
    rw [h]
    rw [Complex.normSq_eq_norm_sq, hw]
    norm_num
  have hstar : star (w - α) = star w - star α := by
    have h := map_sub (starRingEnd ℂ) w α
    simpa only [starRingEnd_apply] using h
  have hrepr : (r : ℂ) * (1 - star α * w / (r : ℂ) ^ 2) =
      w * star (w - α) / (r : ℂ) := by
    rw [hstar]
    field_simp [hr0]
    rw [mul_sub, hww]
    ring
  rw [hrepr, norm_div, norm_mul]
  have hnormr : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_def, Complex.normSq_ofReal]
    exact Real.sqrt_mul_self (le_of_lt hr)
  rw [hnormr, norm_star, hw]
  field_simp [hr0]

end MathlibPlus.Analysis
