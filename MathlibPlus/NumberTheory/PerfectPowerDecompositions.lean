import Mathlib

namespace MathlibPlus.NumberTheory.PerfectPowerDecompositions

/--
Claim 31715.  The positive-natural perfect-power decompositions of `3⁷` are
exactly the trivial one-factor representation and the seven factors of degree
three.  Positivity of the factors and exponent is forced by the displayed
equality and is therefore proved rather than added as an assumption.
-/
theorem degree2187 :
    ∀ m d : ℕ, m ^ d = 3 ^ 7 →
      (m = 2187 ∧ d = 1) ∨ (m = 3 ∧ d = 7) := by
  intro m d h
  have hm : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    cases d <;> norm_num at h
  have hd : 0 < d := by
    by_contra hd
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    subst d
    norm_num at h
  have hmdiv : m ∣ 3 ^ 7 := by
    rw [← h]
    exact dvd_pow_self m (Nat.ne_of_gt hd)
  obtain ⟨k, hk, hmk⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hmdiv
  have hpow : 3 ^ (k * d) = 3 ^ 7 := by
    rw [hmk] at h
    simpa [pow_mul] using h
  have hkd : k * d = 7 :=
    (Nat.pow_right_injective (by norm_num : 2 ≤ (3 : ℕ))) hpow
  have hkcases : k = 1 ∨ k = 7 := by
    interval_cases k <;> omega
  rcases hkcases with rfl | rfl
  · right
    constructor
    · simpa using hmk
    · omega
  · left
    constructor
    · norm_num at hmk ⊢
      exact hmk
    · omega

end MathlibPlus.NumberTheory.PerfectPowerDecompositions
