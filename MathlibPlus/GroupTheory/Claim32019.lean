import Mathlib.GroupTheory.Sylow

namespace MathlibPlus.GroupTheory

/--
If a finite group has order `m * p`, with `m < p` and `p` prime not dividing
`m`, then its Sylow `p`-subgroup is unique and has order `p`.
-/
theorem claim32019_unique_sylow_of_order_mul_prime
    (G : Type*) [Group G] [Finite G]
    (p m : ℕ) (hp : p.Prime) (hm_lt : m < p) (hpm : ¬p ∣ m)
    (hcard : Nat.card G = m * p) :
    ∃ P : Sylow p G, Nat.card (P : Subgroup G) = p ∧
      ∀ Q : Sylow p G, Q = P := by
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p G := Classical.arbitrary _
  letI : P.FiniteIndex := Subgroup.finiteIndex_of_finite
  letI : Finite (Sylow p G) := P.finite_of_finiteIndex
  have hcard_pos : 0 < Nat.card G := Nat.card_pos
  have hm_pos : 0 < m := by
    by_contra hm0
    have hm_zero : m = 0 := Nat.eq_zero_of_not_pos hm0
    rw [hcard, hm_zero] at hcard_pos
    simp at hcard_pos
  have hpdvdG : p ∣ Nat.card G := by
    rw [hcard]
    exact Nat.dvd_mul_left p m
  have hpdvdP : p ∣ Nat.card (P : Subgroup G) := by
    exact P.dvd_card_of_dvd_card hpdvdG
  obtain ⟨k, hk⟩ := hpdvdP
  have hki : k * P.index = m := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    calc
      p * (k * P.index) = (p * k) * P.index := by ac_rfl
      _ = Nat.card (P : Subgroup G) * P.index := by rw [hk]
      _ = Nat.card G := (P : Subgroup G).card_mul_index
      _ = m * p := hcard
      _ = p * m := Nat.mul_comm _ _
  have hindex_dvd_m : P.index ∣ m := by
    refine ⟨k, ?_⟩
    simpa [Nat.mul_comm] using hki.symm
  have hcount_dvd_m : Nat.card (Sylow p G) ∣ m :=
    (P.card_dvd_index).trans hindex_dvd_m
  have hcount_lt : Nat.card (Sylow p G) < p :=
    (Nat.le_of_dvd hm_pos hcount_dvd_m).trans_lt hm_lt
  have hcount_eq_one : Nat.card (Sylow p G) = 1 := by
    exact (card_sylow_modEq_one p G).eq_of_lt_of_lt hcount_lt hp.one_lt
  have hfac : (m * p).factorization p = 1 := by
    rw [Nat.factorization_mul hm_pos.ne' hp.ne_zero]
    simp [Nat.factorization_eq_zero_of_not_dvd hpm, hp.factorization_self]
  have hPcard : Nat.card (P : Subgroup G) = p := by
    rw [P.card_eq_multiplicity, hcard, hfac]
    simp
  refine ⟨P, hPcard, ?_⟩
  have hsub : Subsingleton (Sylow p G) :=
    (Nat.card_eq_one_iff_unique.mp hcount_eq_one).1
  letI : Subsingleton (Sylow p G) := hsub
  exact fun Q => Subsingleton.elim Q P

end MathlibPlus.GroupTheory
