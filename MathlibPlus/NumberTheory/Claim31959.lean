import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace MathlibPlus.NumberTheory.Claim31959

/-- For a prime `p > 3`, the four-block terminal has the displayed totient
formula, and its totient gcd is one exactly in the residue class `2 mod 3`.
-/
theorem arithmeticCondition (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    Nat.totient (3 * p) = 2 * (p - 1) ∧
      (p % 3 = 2 ↔ Nat.gcd (3 * p) (Nat.totient (3 * p)) = 1) := by
  have hcop : Nat.Coprime 3 p := by
    rw [Nat.coprime_comm]
    apply hp.coprime_iff_not_dvd.mpr
    intro h
    have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) h
    omega
  have htot : Nat.totient (3 * p) = 2 * (p - 1) := by
    rw [Nat.totient_mul hcop, Nat.totient_prime hp,
      Nat.totient_prime (by norm_num : Nat.Prime 3)]
  refine ⟨htot, ?_⟩
  rw [htot]
  rw [← Nat.coprime_iff_gcd_eq_one]
  constructor
  · intro hmod
    apply Nat.coprime_of_dvd
    intro q hq hqleft hqright
    rcases hq.dvd_mul.mp hqleft with hq3 | hqp
    · have hqeq : q = 3 :=
        ((Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hq3).resolve_left
          (Nat.ne_of_gt hq.one_lt)
      subst q
      have hthree : ¬3 ∣ p - 1 := by
        intro hd
        obtain ⟨k, hk⟩ := hd
        have hdecomp := Nat.mod_add_div p 3
        have hmod1 : p % 3 = 1 := by
          omega
        omega
      rcases (show Nat.Prime 3 from by norm_num).dvd_mul.mp hqright with h | h
      · norm_num at h
      · exact hthree h
    · have hqeq : q = p :=
        ((Nat.dvd_prime hp).mp hqp).resolve_left (Nat.ne_of_gt hq.one_lt)
      subst q
      rcases hp.dvd_mul.mp hqright with h | h
      · have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
        omega
      · have hpos : 0 < p - 1 := by omega
        have hle : p ≤ p - 1 := Nat.le_of_dvd hpos h
        omega
  · intro hgcd
    by_contra hmod
    have hmod_ne0 : p % 3 ≠ 0 := by
      intro hzero
      have hdiv : 3 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr hzero
      have hpeq : 3 = p :=
        (Nat.dvd_prime_two_le hp (by norm_num : 2 ≤ (3 : ℕ))).mp hdiv
      omega
    have hmod_lt : p % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hmod1 : p % 3 = 1 := by omega
    have hpred : 3 ∣ p - 1 := by
      refine ⟨p / 3, ?_⟩
      have hdecomp := Nat.mod_add_div p 3
      omega
    have hfirst : 3 ∣ 3 * p := by exact dvd_mul_right 3 p
    have hsecond : 3 ∣ 2 * (p - 1) := by exact dvd_mul_of_dvd_right hpred 2
    have hg : 3 ∣ Nat.gcd (3 * p) (2 * (p - 1)) := Nat.dvd_gcd hfirst hsecond
    rw [hgcd] at hg
    norm_num at hg

end MathlibPlus.NumberTheory.Claim31959
