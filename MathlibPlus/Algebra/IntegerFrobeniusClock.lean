import MathlibPlus.Algebra.IntegerEndomorphism
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.NormNum

namespace MathlibPlus.Algebra

/--
Claim 10437 (O-0033), power-clock consequence.  This is stated with the
source's integer base `q > 1`; the exponents remain natural numbers.
-/
theorem no_common_integer_power_clock :
    ¬ ∃ (q : ℤ) (a b : ℕ), 1 < q ∧ q ^ a = 2 ∧ q ^ b = 3 := by
  rintro ⟨q, a, b, hq, ha, hb⟩
  have hq0 : 0 ≤ q :=
    (show (0 : ℤ) ≤ 1 by norm_num).trans (le_of_lt hq)
  have hqcast : (q.natAbs : ℤ) = q := Int.natAbs_of_nonneg hq0
  have hq_nat : 1 < q.natAbs := by
    have hq' : (1 : ℤ) < (q.natAbs : ℤ) := by simpa [hqcast] using hq
    exact_mod_cast hq'
  have ha_nat : q.natAbs ^ a = 2 := by
    have h := congrArg Int.natAbs ha
    simpa [Int.natAbs_pow] using h
  have hb_nat : q.natAbs ^ b = 3 := by
    have h := congrArg Int.natAbs hb
    simpa [Int.natAbs_pow] using h
  have ha0 : 0 < a := by
    by_contra h
    have ha_eq : a = 0 := Nat.eq_zero_of_not_pos h
    simp [ha_eq] at ha_nat
  have hq_le : q.natAbs ≤ q.natAbs ^ a := Nat.le_pow ha0
  have hq_le_two : q.natAbs ≤ 2 := by simpa [ha_nat] using hq_le
  have hq_two_le : 2 ≤ q.natAbs := (Nat.succ_le_iff).2 hq_nat
  have hq_eq : q.natAbs = 2 := Nat.le_antisymm hq_le_two hq_two_le
  have hb_two : 2 ^ b = 3 := by simpa [hq_eq] using hb_nat
  have hb0 : b ≠ 0 := by
    intro hb_eq
    simp [hb_eq] at hb_two
  have hdiv : 2 ∣ 2 ^ b := dvd_pow_self 2 hb0
  rw [hb_two] at hdiv
  norm_num at hdiv

end MathlibPlus.Algebra
