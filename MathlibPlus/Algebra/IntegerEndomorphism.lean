import Mathlib

/-!
# Integer endomorphisms and incompatible common powers

The two elementary statements in admitted claim 12684 are recorded without
identifying a family of local Frobenii with a global endomorphism.
-/

namespace MathlibPlus.Algebra.IntegerEndomorphism

theorem int_ringHom_apply (f : ℤ →+* ℤ) (z : ℤ) : f z = z := by
  simpa using (map_intCast f z)

theorem int_ringHom_eq_id (f : ℤ →+* ℤ) : f = RingHom.id ℤ := by
  exact RingHom.ext_int f (RingHom.id ℤ)

theorem no_common_integer_power (q : ℤ) (a b : ℕ)
    (hq : 1 < q) (ha : 0 < a) (hb : 0 < b)
    (hqa : q ^ a = 2) (hqb : q ^ b = 3) : False := by
  have hq_dvd_2 : q ∣ (2 : ℤ) := by
    rw [← hqa]
    exact dvd_pow_self q (Nat.ne_of_gt ha)
  have hq_le : q ≤ 2 := Int.le_of_dvd (by norm_num) hq_dvd_2
  have hq_eq : q = 2 := by omega
  have hq_dvd_3 : q ∣ (3 : ℤ) := by
    rw [← hqb]
    exact dvd_pow_self q (Nat.ne_of_gt hb)
  rw [hq_eq] at hq_dvd_3
  norm_num at hq_dvd_3

end MathlibPlus.Algebra.IntegerEndomorphism
