import Mathlib

namespace MathlibPlus.Analysis.Claim19553

/-- The constant coefficient displayed in claim 19553 is strictly negative. -/
theorem shiftedConstantCoefficientNegative_claim19553 :
    6 / Real.pi - 7 / 2 < 0 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  rw [sub_neg]
  rw [div_lt_iff₀ hpi]
  nlinarith

/-- A coefficient equal to the displayed constant rules out coefficientwise
nonnegativity, without importing an unstated definition of the source
polynomial. -/
theorem notCoefficientwiseNonnegative_claim19553
    (p : ℕ → ℝ) (h₀ : p 0 = 6 / Real.pi - 7 / 2) :
    ¬ (∀ n, 0 ≤ p n) := by
  intro hnonneg
  have h := hnonneg 0
  rw [h₀] at h
  linarith [shiftedConstantCoefficientNegative_claim19553]

end MathlibPlus.Analysis.Claim19553
