import Mathlib

namespace MathlibPlus.NumberTheory

/--
For the standard base-`b`, multiplier-`m` carry transition, every state
`c < m` and digit `d < b` produces a next carry below `m`.
-/
theorem carryStateClosed (b m c d : ℕ)
    (hb : 2 ≤ b) (hm : 2 ≤ m) (hc : c < m) (hd : d < b) :
    (m * d + c) / b < m := by
  have hmpos : 0 < m := Nat.zero_lt_of_lt hm
  have hmd : m * d < m * b := Nat.mul_lt_mul_of_pos_left hd hmpos
  have h1 : m * d + c < m * d + m := Nat.add_lt_add_left hc _
  have h2 : m * d + m ≤ m * b := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left m (Nat.succ_le_of_lt hd)
  have hsum : m * d + c < m * b := lt_of_lt_of_le h1 h2
  exact (Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt hb)).2 hsum

end MathlibPlus.NumberTheory
