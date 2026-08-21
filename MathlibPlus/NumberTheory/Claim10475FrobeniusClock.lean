import MathlibPlus.Algebra.IntegerEndomorphism

namespace MathlibPlus.NumberTheory

/-- No integer base greater than one can make both 2 and 3 positive powers of
that same base. -/
theorem no_common_nat_power_claim10475
    {q a b : ℕ} (_hq : 1 < q) (h₂ : 2 = q ^ a) (h₃ : 3 = q ^ b) :
    False := by
  have hqa : q = 2 ∧ a = 1 :=
    (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 2)).mp h₂.symm
  have hq2 : q = 2 := hqa.1
  rw [hq2] at h₃
  have hb : b ≠ 0 := by
    intro hb
    subst b
    norm_num at h₃
  have hd : 2 ∣ 2 ^ b := dvd_pow_self 2 hb
  rw [← h₃] at hd
  norm_num at hd

end MathlibPlus.NumberTheory
