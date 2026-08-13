import Mathlib

namespace MathlibPlus.NumberTheory

/-- Claim 4035: distinct-prime power quotients have unique logarithmic labels. -/
theorem crossPrimeLagLabeling
    (p q p' q' k l k' l' : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hp' : p'.Prime) (hq' : q'.Prime)
    (hpq : p ≠ q) (hp'q' : p' ≠ q')
    (hk : 1 ≤ k) (hl : 1 ≤ l) (hk' : 1 ≤ k') (hl' : 1 ≤ l')
    (hlog : Real.log ((p : ℝ)^k / (q : ℝ)^l) =
      Real.log ((p' : ℝ)^k' / (q' : ℝ)^l')) :
    (p, k, q, l) = (p', k', q', l') := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hp'R : (0 : ℝ) < p' := by exact_mod_cast hp'.pos
  have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'.pos
  have hp_pos : 0 < (p : ℝ)^k / (q : ℝ)^l :=
    div_pos (pow_pos hpR _) (pow_pos hqR _)
  have hp'_pos : 0 < (p' : ℝ)^k' / (q' : ℝ)^l' :=
    div_pos (pow_pos hp'R _) (pow_pos hq'R _)
  have hratio : (p : ℝ)^k / (q : ℝ)^l =
      (p' : ℝ)^k' / (q' : ℝ)^l' := by
    have hexp := congrArg Real.exp hlog
    simpa [Real.exp_log hp_pos, Real.exp_log hp'_pos] using hexp
  have hprodR : (p : ℝ)^k * (q' : ℝ)^l' =
      (p' : ℝ)^k' * (q : ℝ)^l := by
    exact (div_eq_div_iff (ne_of_gt (pow_pos hqR _))
      (ne_of_gt (pow_pos hq'R _))).mp hratio
  have hprod : p^k * q'^l' = p'^k' * q^l := by
    exact_mod_cast hprodR
  have hp_dvd_rhs : p ∣ p'^k' * q^l := by
    rw [← hprod]
    exact dvd_mul_of_dvd_left (dvd_pow_self p (Nat.ne_of_gt hk)) _
  have hp_cases : p ∣ p' ∨ p ∣ q := by
    rcases (hp.dvd_mul).mp hp_dvd_rhs with h | h
    · exact Or.inl (hp.dvd_of_dvd_pow h)
    · exact Or.inr (hp.dvd_of_dvd_pow h)
  have hpp' : p = p' := by
    rcases hp_cases with h | h
    · exact ((hp'.dvd_iff_eq hp.ne_one).mp h).symm
    · exact False.elim (hpq ((hq.dvd_iff_eq hp.ne_one).mp h).symm)
  have hq_dvd_lhs : q ∣ p^k * q'^l' := by
    rw [hprod]
    exact dvd_mul_of_dvd_right (dvd_pow_self q (Nat.ne_of_gt hl)) _
  have hq_cases : q ∣ p ∨ q ∣ q' := by
    rcases (hq.dvd_mul).mp hq_dvd_lhs with h | h
    · exact Or.inl (hq.dvd_of_dvd_pow h)
    · exact Or.inr (hq.dvd_of_dvd_pow h)
  have hqq' : q = q' := by
    rcases hq_cases with h | h
    · exact False.elim (hpq ((hp.dvd_iff_eq hq.ne_one).mp h))
    · exact ((hq'.dvd_iff_eq hq.ne_one).mp h).symm
  subst p'
  subst q'
  have hp_not_dvd_q : ¬p ∣ q := by
    intro h
    exact hpq ((hq.dvd_iff_eq hp.ne_one).mp h).symm
  have hq_not_dvd_p : ¬q ∣ p := by
    intro h
    exact hpq ((hp.dvd_iff_eq hq.ne_one).mp h)
  have hpq_coprime : (p^k).Coprime (q^l) := by
    exact (hp.coprime_iff_not_dvd.mpr hp_not_dvd_q).pow_left k |>.pow_right l
  have hpk_dvd : p^k ∣ p^k' := by
    apply hpq_coprime.dvd_of_dvd_mul_right
    rw [← hprod]
    exact dvd_mul_right _ _
  have hpk'_dvd : p^k' ∣ p^k := by
    have hcop : (p^k').Coprime (q^l') := by
      exact (hp.coprime_iff_not_dvd.mpr hp_not_dvd_q).pow_left k' |>.pow_right l'
    apply hcop.dvd_of_dvd_mul_right
    rw [hprod]
    exact dvd_mul_right _ _
  have hpowp : p^k = p^k' := Nat.dvd_antisymm hpk_dvd hpk'_dvd
  have hkk' : k = k' := Nat.pow_right_injective hp.two_le hpowp
  have hql_dvd : q^l ∣ q^l' := by
    have hcop : (q^l).Coprime (p^k) := by
      exact (hq.coprime_iff_not_dvd.mpr hq_not_dvd_p).pow_left l |>.pow_right k
    apply hcop.dvd_of_dvd_mul_left
    rw [hprod]
    exact dvd_mul_left _ _
  have hql'_dvd : q^l' ∣ q^l := by
    have hcop : (q^l').Coprime (p^k') := by
      exact (hq.coprime_iff_not_dvd.mpr hq_not_dvd_p).pow_left l' |>.pow_right k'
    apply hcop.dvd_of_dvd_mul_left
    rw [← hprod]
    exact dvd_mul_left _ _
  have hpowq : q^l = q^l' := Nat.dvd_antisymm hql_dvd hql'_dvd
  have hll' : l = l' := Nat.pow_right_injective hq.two_le hpowq
  subst k'
  subst l'
  rfl

end MathlibPlus.NumberTheory
