import Mathlib

namespace MathlibPlus.Algebra

/-- Clearing the two nonzero denominators in the type-IV quotient equation from
admitted claim 9284. -/
theorem cleared_typeIV_quotient_equivalence_claim9284
    {K : Type*} [Field K] {P Q z : K}
    (hz_one : z ≠ 1) (hz_neg_one : z ≠ -1) (hP : P ≠ 0) :
    Q / ((z - 1) * P) = 2 / (z + 1) ↔
      (z + 1) * Q - 2 * (z - 1) * P = 0 := by
  have hleft : (z - 1) * P ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hz_one) hP
  have hright : z + 1 ≠ 0 := by
    intro h
    exact hz_neg_one (eq_neg_of_add_eq_zero_left h)
  rw [div_eq_div_iff hleft hright]
  constructor <;> intro h <;> linear_combination h

end MathlibPlus.Algebra
