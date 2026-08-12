import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace MathlibPlus.NumberTheory.Claim50193

lemma factorization_two_mul {u a : ℕ} (hu : 0 < u) :
    (2 ^ a * u).factorization 2 = a + u.factorization 2 := by
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hu.ne']
  have htwo : Nat.factorization 2 2 = 1 := by
    simpa using (Nat.Prime.factorization_self (by norm_num : Nat.Prime 2))
  simp [htwo]

lemma oddpart_pow_mul {u a : ℕ} (hu : 0 < u) :
    (2 ^ a * u) / 2 ^ (2 ^ a * u).factorization 2 =
      u / 2 ^ u.factorization 2 := by
  rw [factorization_two_mul hu, pow_add]
  rw [Nat.mul_div_mul_left]
  exact Nat.pow_pos (by norm_num : 0 < (2 : ℕ))

lemma oddpart_opposite {u a : ℕ} (hu : 0 < u) (ha : 2 ≤ a) :
    (2 ^ a * u - 2 + 2) / 2 ^ (2 ^ a * u - 2 + 2).factorization 2 =
      u / 2 ^ u.factorization 2 := by
  have hbound : 2 ≤ 2 ^ a * u := by
    have hpow : 2 ≤ 2 ^ a := by
      calc
        2 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ a := by
          exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) ha
    exact hpow.trans (Nat.le_mul_of_pos_right _ hu)
  simp only [Nat.sub_add_cancel hbound]
  rw [factorization_two_mul hu, pow_add]
  rw [Nat.mul_div_mul_left]
  exact Nat.pow_pos (by norm_num : 0 < (2 : ℕ))

lemma endpoint_moduli {u a : ℕ} (hu : 0 < u) (ha : 2 ≤ a) :
    (2 ^ a * u) % 4 = 0 ∧ (2 ^ a * u - 2) % 4 = 2 := by
  have haeq : a = (a - 2) + 2 := by omega
  have h4 : 4 ∣ 2 ^ a := by
    rw [haeq, pow_add]
    norm_num
  have hzero : (2 ^ a * u) % 4 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left h4 u)
  have hbound : 2 ≤ 2 ^ a * u := by
    have hpow : 2 ≤ 2 ^ a := by
      calc
        2 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ a := by
          exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) ha
    exact hpow.trans (Nat.le_mul_of_pos_right _ hu)
  constructor
  · exact hzero
  · omega

/-- For a final sign run with half-gap `u`, the same-sign endpoint is
`2^a*u` and the opposite-sign endpoint is `2^a*u - 2`; the orientation-aware
odd-part coordinate has the same value in both cases.  The odd part is written
inline as `n / 2^(v₂(n))`, with `v₂` represented by `n.factorization 2`. -/
theorem endpoint_oddPart_invariant {u a : ℕ} (hu : 0 < u) (ha : 2 ≤ a) :
    let oddPart : ℕ → ℕ := fun n => n / 2 ^ n.factorization 2
    let p : ℕ → ℕ := fun H =>
      if H % 4 = 0 then oddPart H else oddPart (H + 2)
    p (2 ^ a * u) = oddPart u ∧
      p (2 ^ a * u - 2) = oddPart u := by
  dsimp
  obtain ⟨hsame, hopposite⟩ := endpoint_moduli hu ha
  constructor
  · rw [if_pos hsame]
    exact oddpart_pow_mul hu
  · have hnot : (2 ^ a * u - 2) % 4 ≠ 0 := by omega
    rw [if_neg hnot]
    exact oddpart_opposite hu ha

end MathlibPlus.NumberTheory.Claim50193
