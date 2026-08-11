import Mathlib

namespace MathlibPlus.Algebra.TelescopingFractions

/-- Claim 25650: the two displayed finite sums have the stated closed forms.
The omitted scalar convention is fixed here as exact rational arithmetic. -/
theorem telescopingClosedForms (R : ℕ) (hR : 1 ≤ R) :
    (2 - 2 * ∑ r ∈ Finset.Icc 1 R, (1 : ℚ) / (r * (r + 1))) = 2 / (R + 1) ∧
      (∑ r ∈ Finset.Icc 1 R,
          ((2 * r + 1 : ℚ) ^ 2) / (r * (r + 1))) =
        (R : ℚ) * (4 * R + 5) / (R + 1) := by
  induction R, hR using Nat.le_induction with
  | base =>
      norm_num
  | succ R hR ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      constructor
      · have h := ih.1
        push_cast at h ⊢
        field_simp at h ⊢
        nlinarith [h]
      · rw [Finset.sum_Icc_succ_top (by omega)]
        have h := ih.2
        push_cast at h ⊢
        field_simp at h ⊢
        nlinarith [h]

end MathlibPlus.Algebra.TelescopingFractions
