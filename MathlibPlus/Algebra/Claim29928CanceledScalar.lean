import Mathlib

namespace MathlibPlus.Algebra

/-- Claim 29928: the reciprocal scalar node lies strictly outside the
interval spanned by the nonbase nodes `0, 1, 2`. -/
theorem canceled_scalar_node_outside_interval (c : ℝ)
    (hc0 : c ≠ 0) (hcm : c ≠ -1) (hcp : c ≠ 1) :
    let δ : ℝ := 1 + (c + c⁻¹) / 2
    (c < 0 → δ < 0) ∧
      (0 < c → 2 < δ) ∧
      (δ < 0 ∨ 2 < δ) := by
  dsimp
  have hneg : c < 0 → 1 + (c + c⁻¹) / 2 < 0 := by
    intro hc
    have hne : c + 1 ≠ 0 := by
      intro h
      apply hcm
      linarith
    have hsq : 0 < (c + 1) ^ 2 := sq_pos_of_ne_zero hne
    have hid : c + c⁻¹ + 2 = (c + 1) ^ 2 / c := by
      field_simp [hc0]
      ring
    have hquot : (c + 1) ^ 2 / c < 0 := div_neg_of_pos_of_neg hsq hc
    calc
      1 + (c + c⁻¹) / 2 = (c + c⁻¹ + 2) / 2 := by ring
      _ = ((c + 1) ^ 2 / c) / 2 := by rw [hid]
      _ < 0 := by linarith
  have hpos : 0 < c → 2 < 1 + (c + c⁻¹) / 2 := by
    intro hc
    have hne : c - 1 ≠ 0 := sub_ne_zero.mpr hcp
    have hsq : 0 < (c - 1) ^ 2 := sq_pos_of_ne_zero hne
    have hid : c + c⁻¹ - 2 = (c - 1) ^ 2 / c := by
      field_simp [hc0]
      ring
    have hquot : 0 < (c - 1) ^ 2 / c := div_pos hsq hc
    have hrepr : 1 + (c + c⁻¹) / 2 =
        2 + (c + c⁻¹ - 2) / 2 := by ring
    rw [hrepr, hid]
    linarith
  constructor
  · exact hneg
  constructor
  · exact hpos
  · rcases lt_or_gt_of_ne hc0 with hc | hc
    · exact Or.inl (hneg hc)
    · exact Or.inr (hpos hc)

end MathlibPlus.Algebra
