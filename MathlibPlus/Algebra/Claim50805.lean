import Mathlib.Tactic

namespace MathlibPlus.Algebra

/-- The reflected positive scalar has a nonnegative defect at every natural power.
The inverse of `r ^ k` is Lean's direct encoding of the displayed `r ^ (-k)`. -/
theorem reflected_power_defect_claim50805 (r : ℝ) (hr : 0 < r) (k : ℕ)
    (_hk : 1 ≤ k) :
    r ^ k + (r ^ k)⁻¹ - 2 = (r ^ k - 1) ^ 2 / r ^ k ∧
      0 ≤ r ^ k + (r ^ k)⁻¹ - 2 := by
  have hp : 0 < r ^ k := pow_pos hr k
  have hid : r ^ k + (r ^ k)⁻¹ - 2 = (r ^ k - 1) ^ 2 / r ^ k := by
    field_simp [ne_of_gt hp]
    ring
  constructor
  · exact hid
  · rw [hid]
    exact div_nonneg (sq_nonneg _) (le_of_lt hp)

/-- At the first power, the reflected defect vanishes exactly at balance. -/
theorem reflected_first_defect_eq_zero_iff_claim50805 (r : ℝ) (hr : 0 < r) :
    r ^ (1 : ℕ) + (r ^ (1 : ℕ))⁻¹ - 2 = 0 ↔ r = 1 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hid : r ^ (1 : ℕ) + (r ^ (1 : ℕ))⁻¹ - 2 = (r - 1) ^ 2 / r := by
    field_simp [hr0]
    ring
  rw [hid]
  constructor
  · intro h
    have hs : (r - 1) ^ 2 = 0 := by
      exact (div_eq_zero_iff).mp h |>.resolve_right hr0
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  · intro h
    simp [h]

end MathlibPlus.Algebra
