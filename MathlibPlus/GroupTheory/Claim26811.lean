import Mathlib

namespace MathlibPlus.GroupTheory

/-- The central half-turn identities in the dihedral group of order `4 * m`.
The parity clause records the source's separate assertion about an even `m`. -/
theorem dihedralHalfTurn_claim26811 (m : ℕ) (hm : 2 ≤ m) :
    (Even m → (m : ZMod 2) = 0) ∧
      (m : ZMod (2 * m)) + (m : ZMod (2 * m)) = 0 ∧
      -(m : ZMod (2 * m)) = (m : ZMod (2 * m)) ∧
      orderOf (DihedralGroup.r (m : ZMod (2 * m))) = 2 := by
  have hparity : Even m → (m : ZMod 2) = 0 := by
    rintro ⟨k, hk⟩
    calc
      (m : ZMod 2) = ((k + k : ℕ) : ZMod 2) := by rw [← hk]
      _ = ((2 * k : ℕ) : ZMod 2) := by rw [two_mul]
      _ = 0 := by rw [Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have hmod : (2 * m : ℕ) ≠ 0 := by omega
  letI : NeZero (2 * m) := ⟨hmod⟩
  have hadd : (m : ZMod (2 * m)) + (m : ZMod (2 * m)) = 0 := by
    calc
      (m : ZMod (2 * m)) + (m : ZMod (2 * m)) =
          ((m + m : ℕ) : ZMod (2 * m)) := (Nat.cast_add m m).symm
      _ = ((2 * m : ℕ) : ZMod (2 * m)) := by rw [two_mul]
      _ = 0 := ZMod.natCast_self (2 * m)
  have hneg : -(m : ZMod (2 * m)) = (m : ZMod (2 * m)) := by
    rw [neg_eq_iff_add_eq_zero]
    exact hadd
  have horder : orderOf (DihedralGroup.r (m : ZMod (2 * m))) = 2 := by
    rw [DihedralGroup.orderOf_r]
    have hval : (m : ZMod (2 * m)).val = m := by
      apply ZMod.val_natCast_of_lt
      omega
    rw [hval]
    have hgcd : (2 * m).gcd m = m := by
      apply Nat.gcd_eq_right_iff_dvd.mpr
      simpa [Nat.mul_comm] using (Nat.dvd_mul_right m 2)
    rw [hgcd]
    simpa [Nat.mul_comm] using (Nat.mul_div_cancel_left 2 (by omega : 0 < m))
  exact ⟨hparity, hadd, hneg, horder⟩

end MathlibPlus.GroupTheory
