import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace MathlibPlus.Algebra.Claim55055

/-- Equal first two Vieta coefficients determine the unordered pair of roots. -/
theorem equal_sum_product_pair
    {a b c d : ℝ}
    (hsum : a + b = c + d) (hprod : a * b = c * d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hb : b = c + d - a := by
    calc
      b = (a + b) - a := by ring
      _ = (c + d) - a := by rw [hsum]
  have hp : a * (c + d - a) = c * d := by
    rw [← hb]
    exact hprod
  have hfactor : (a - c) * (a - d) = 0 := by
    calc
      (a - c) * (a - d) = c * d - a * (c + d - a) := by ring
      _ = 0 := by rw [hp]; ring
  rcases mul_eq_zero.mp hfactor with hac | had
  · left
    constructor
    · exact sub_eq_zero.mp hac
    · calc
        b = c + d - a := hb
        _ = d := by rw [sub_eq_zero.mp hac]; ring
  · right
    constructor
    · exact sub_eq_zero.mp had
    · calc
        b = c + d - a := hb
        _ = c := by rw [sub_eq_zero.mp had]; ring

end MathlibPlus.Algebra.Claim55055
